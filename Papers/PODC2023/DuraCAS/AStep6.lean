import Papers.PODC2023.DuraCAS.AStep5

/-!
# Preservation of the global invariant: the steps of a process, case by case
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem next_ret {a : AS P K V} {p : P} {r : OpRec K V} (hop : (a.ps p).op = some r) (resp : Resp V) :
    a.next p (.ret resp) = a.fin p (.ret r.id resp (a.ls (p, .crit))) := by
  simp [AS.next, AS.fin, hop]

theorem next_rdone {a : AS P K V} {p : P} {r : OpRec K V} (hop : (a.ps p).op = some r) :
    a.next p .rdone = a.fin p (.rdone r.id (a.ls (p, .crit))) := by
  simp [AS.next, AS.fin, hop]

theorem GInv.goStep {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (pc' : Pc V)
    (hl : Loc p (view init a g r.k) { pview a g p r with pc := .at pc' }) :
    ∃ g', GInv init (a.next p (.go pc')) g' := ⟨g, h.go hop _ (by simp [hop]) hl⟩

theorem GInv.goStepAft {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (pc' : APc V)
    (hl : Loc p (view init a g r.k) { pview a g p r with pc := pc' }) :
    ∃ g', GInv init { a with ps := Function.update a.ps p { a.ps p with pc := pc' } } g' :=
  ⟨g, h.go hop _ (by simp [hop]) hl⟩

theorem GInv.orph_none_at {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {c : APc V} (hpc : (a.ps p).pc = c)
    (hc : ∀ j, c ≠ .at (.recv j)) : (a.ps p).orph = none :=
  (h.loc p r hop).orph_none (by intro j; show (a.ps p).pc ≠ _; rw [hpc]; exact hc j)

theorem GInv.pw_nw {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (hw : ¬ IsWr r.op) :
    g.pw r.k ≠ some r.id := fun e => hw ⟨_, ((h.loc p r hop).pw_op e).2⟩

theorem GInv.pcok {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {c : APc V} (hpc : (a.ps p).pc = c) :
    PcOK (view init a g r.k) (pview a g p r) c := by
  have := (h.loc p r hop).pc; rw [show (pview a g p r).pc = (a.ps p).pc from rfl, hpc] at this
  exact this

theorem step_read {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (hpc : (a.ps p).pc = .at .read) :
    ∃ g', GInv init (apstep a p) g' := by
  obtain ⟨hopr, hls⟩ := h.pcok hop hpc
  have hopr' : r.op = .read := hopr
  have hsig : curSt init g.L r.k = (a.Y (r.k, .Z)).2.1 := (h.kinv r.k).sig_eq
  simp only [apstep, hop, hpc]
  rw [next_ret hop]
  exact ⟨_, h.mainret hop (h.orph_none_at hop hpc (by simp)) (h.pw_nw hop (by simp [hopr', IsWr]))
    hls _ (by rw [hopr']; simp [seqStep, hsig])⟩

theorem step_cas7 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {i : Bool} (hpc : (a.ps p).pc = .at (.cas7 i)) :
    ∃ g', GInv init (apstep a p) g' := by
  obtain ⟨⟨old, new, hopr⟩, hls, -⟩ := h.pcok hop hpc
  have hopr' : r.op = .cas old new := hopr
  have hsig : curSt init g.L r.k = (a.Y (r.k, .Z)).2.1 := (h.kinv r.k).sig_eq
  have ho := h.orph_none_at hop hpc (by simp)
  have hpw := h.pw_nw hop (by simp [hopr', IsWr])
  simp only [apstep, hop, hpc, hopr']
  split_ifs with h1 h2
  · rw [next_ret hop]
    exact ⟨_, h.mainret hop ho hpw hls _ (by rw [hopr']; simp [seqStep, hsig, h1])⟩
  · rw [next_ret hop]
    have h1' : (a.Y (r.k, .Z)).2.1 = old := not_not.1 h1
    exact ⟨_, h.mainret hop ho hpw hls _ (by rw [hopr']; simp [seqStep, hsig, h1', h2])⟩
  · exact h.goStep hop _ (go_cas7 (h.loc p r hop) hpc hopr (not_not.1 h1) h2)

theorem step_wr12 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (hpc : (a.ps p).pc = .at .wr12) :
    ∃ g', GInv init (apstep a p) g' := by
  simp only [apstep, hop, hpc]
  exact h.goStep hop _ (go_wr12 (h.loc p r hop) hpc)

theorem step_wr13 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {w : Cell V} (hpc : (a.ps p).pc = .at (.wr13 w)) :
    ∃ g', GInv init (apstep a p) g' := by
  obtain ⟨⟨u, hopr⟩, hls, -⟩ := h.pcok hop hpc
  have hopr' : r.op = .write u := hopr
  have hsig : curSt init g.L r.k = (a.Y (r.k, .Z)).2.1 := (h.kinv r.k).sig_eq
  have hl := h.loc p r hop
  simp only [apstep, hop, hpc, hopr']
  split_ifs with h1 h2
  · rw [next_ret hop]
    have hpw : g.pw r.k ≠ some r.id := fun e => by
      have := (hl.pw_op e).1; simp only [pview] at this hls; omega
    exact ⟨_, h.mainret hop (h.orph_none_at hop hpc (by simp)) hpw hls _
      (by rw [hopr']; simp [seqStep, hsig, h1])⟩
  · exact h.goStep hop _ (go_wr13_15 hl hpc hopr h1 h2)
  · exact h.goStep hop _ (go_wr13_19 hl (h.kinv r.k) hpc h2)

theorem step_tw19 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {ret : Ret V}
    (hpc : (a.ps p).pc = .at (.tw19 ret)) : ∃ g', GInv init (apstep a p) g' := by
  simp only [apstep, hop, hpc]
  exact h.goStep hop _ (go_tw19 (h.loc p r hop) (h.kinv r.k) hpc)

/-- A write at the end of its second transfer does not need a move any more. -/
theorem GInv.wretStep {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {c : APc V} (hpc : (a.ps p).pc = c)
    (hc : ∀ j, c ≠ .at (.recv j)) (hwr : IsWr r.op)
    (hneed : ¬ needW (view init a g r.k) (pview a g p r)) :
    ∃ g', GInv init (a.next p (.ret (.ok true))) g' := by
  rw [next_ret hop]; exact h.wret hop (h.orph_none_at hop hpc hc) hwr hneed

theorem GInv.rdoneStep {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {c : APc V} (hpc : (a.ps p).pc = c)
    (hc : ∀ j, c ≠ .at (.recv j)) (hneed : g.pw r.k ≠ some r.id) :
    ∃ g', GInv init (a.next p .rdone) g' := by
  rw [next_rdone hop]
  exact ⟨_, h.done_noL hop (h.orph_none_at hop hpc hc) hneed _ ⟨rfl, rfl, by intros; simp⟩
    (fun id resp d he => by simp at he)⟩

theorem step_tw20 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {ret : Ret V} {zh : Cell V}
    (hpc : (a.ps p).pc = .at (.tw20 ret zh)) : ∃ g', GInv init (apstep a p) g' := by
  have hl := h.loc p r hop
  have hok := h.pcok hop hpc
  simp only [apstep, hop, hpc]
  split_ifs with hb
  · exact h.goStep hop _ (go_tw20_21 hl hpc hb)
  · have hb' : zh.2.2 = (a.Y (r.k, .W)).2.2 := not_not.1 hb
    obtain ⟨hg, hm⟩ := hok
    simp only [TwGen] at hg
    -- if the write still needed a move, `Z = zh` and the bits would differ
    have hnd : ∀ need : Prop, (need → (view init a g r.k).pend) →
        (need → (True → (view init a g r.k).zAt < zh.1 ∧ (view init a g r.k).Z = zh)) → ¬need := by
      intro need h1 h2 hn
      apply h1 hn
      show (a.Y (r.k, .W)).2.2 = (a.Y (r.k, .Z)).2.2
      have hz : a.Y (r.k, .Z) = zh := (h2 hn trivial).2
      rw [hz, hb']
    rcases ret with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only [Stage] at hm
    · exact h.goStep hop _ (go_tw20_ret hl hpc hb' rfl)
    · exact h.goStep hop _ (go_tw20_ret hl hpc hb' rfl)
    · exact h.wretStep hop hpc (by simp) hm.1 (hnd _ hm.2.1 (fun hn => (hm.2.2 hn).1))
    · exact h.goStep hop _ (go_tw20_ret hl hpc hb' rfl)
    · exact h.rdoneStep hop hpc (by simp) (hnd _ hm.1 (fun hn => (hm.2 hn).1))

theorem step_recv {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {j : Fin 4} (hpc : (a.ps p).pc = .at (.recv j))
    (hen : ∀ x, (a.ps p).orph = some x → x.o ≠ recObj r.k j) :
    ∃ g', GInv init (apstep a p) g' := by
  simp only [apstep, hop, hpc]
  have : ∃ pc', afterCall (.recv j : Pc V) false = .go pc' := by
    simp only [afterCall]; split_ifs <;> exact ⟨_, rfl⟩
  obtain ⟨pc', hpc'⟩ := this
  rw [hpc']
  exact h.goStep hop _ (go_recv (h.loc p r hop) (h.kinv r.k) hpc hen hpc')

theorem step_cas10 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {i : Bool} {z : Cell V}
    (hpc : (a.ps p).pc = .at (.cas10 i z)) : ∃ g', GInv init (apstep a p) g' := by
  have hl := h.loc p r hop
  obtain ⟨⟨old, new, hopr, hm⟩, -⟩ := h.pcok hop hpc
  have hopr' : r.op = .cas old new := hopr
  simp only [apstep, hop, hpc, hopr', scArgs]
  by_cases hZ : (a.Y (r.k, .Z)).1 = z.1
  · simp only [ecsc, hZ, ↓reduceIte]
    have hls : a.ls (p, .crit) = r.d1 := hm.1
    obtain ⟨hI, hact⟩ := impr_actor g.clk (max (a.ls (p, .crit)) z.1 + 1) hl (h.kinv r.k) hpc hopr hZ
      (by show a.ls (p, .crit) < _; omega) (by show (a.Y (r.k, .Z)).1 < _; omega)
    have hsig : curSt init g.L r.k = old := by
      have h1 : curSt init g.L r.k = (a.Y (r.k, .Z)).2.1 := (h.kinv r.k).sig_eq
      have h2 : z = a.Y (r.k, .Z) := hm.2.2.2.1.2 hZ.symm
      rw [h1, ← h2]; exact hm.2.1
    have hninL : r.id ∉ g.L.map GE.id := fun hin => by
      have := hl.inL_lt hin; simp only [pview] at this; omega
    exact ⟨_, h.impr hop hopr' hsig hninL _ (by simp [hop]) _ z.2.2 hI hact⟩
  · simp only [ecsc, hZ, ↓reduceIte]
    exact ⟨g, h.go hop _ rfl (fail_cas10 hl hpc hZ)⟩

theorem step_wr15 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {w : Cell V}
    (hpc : (a.ps p).pc = .at (.wr15 w)) : ∃ g', GInv init (apstep a p) g' := by
  have hl := h.loc p r hop
  obtain ⟨⟨u, hopr, -⟩, hls, -⟩ := h.pcok hop hpc
  have hopr' : r.op = .write u := hopr
  simp only [apstep, hop, hpc, hopr', scArgs]
  by_cases hW : (a.Y (r.k, .W)).1 = w.1
  · simp only [ecsc, hW, ↓reduceIte]
    obtain ⟨hI, hact⟩ := inst_actor (max (a.ls (p, .crit)) w.1 + 1) hl hpc hopr hW
      (by show a.ls (p, .crit) < _; omega) (by omega)
    exact ⟨_, h.inst hop _ (by simp [hop]) _ _ hI hact⟩
  · simp only [ecsc, hW, ↓reduceIte]
    exact ⟨g, h.go hop _ rfl (fail_wr15 hl hpc hW)⟩

theorem step_tw21 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {ret : Ret V} {zh wh : Cell V}
    (hpc : (a.ps p).pc = .at (.tw21 ret zh wh)) : ∃ g', GInv init (apstep a p) g' := by
  have hl := h.loc p r hop
  obtain ⟨hg, -⟩ := h.pcok hop hpc
  simp only [TwGen] at hg
  simp only [apstep, hop, hpc, scArgs]
  by_cases hZ : (a.Y (r.k, .Z)).1 = zh.1
  · simp only [ecsc, hZ, ↓reduceIte]
    obtain ⟨hM, hact⟩ := move_actor g.clk (max (a.ls (p, .cas)) zh.1 + 1) hl (h.kinv r.k) hpc hZ
      (by omega)
    have hp : (view init a g r.k).pend := (hg.2.2 hZ).2
    obtain ⟨idw, hidw⟩ := Option.ne_none_iff_exists'.1 ((h.kinv r.k).pend_iff.1 hp)
    exact ⟨_, h.move hop hidw _ (by simp [hop]) _ _ hM hact⟩
  · simp only [ecsc, hZ, ↓reduceIte]
    exact ⟨g, h.go hop _ rfl (fail_tw21 hl hpc hZ)⟩

theorem step_aft_cas10 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {i b : Bool} {z : Cell V}
    (hpc : (a.ps p).pc = .aft (.cas10 i z) b) : ∃ g', GInv init (apstep a p) g' := by
  have hl := h.loc p r hop
  obtain ⟨⟨old, new, hopr⟩, hb1, hb2⟩ := h.pcok hop hpc
  have hopr' : r.op = .cas old new := hopr
  have ho := h.orph_none_at hop hpc (by simp)
  have hpw := h.pw_nw hop (by simp [hopr', IsWr])
  simp only [apstep, hop, hpc, afterCall]
  cases b
  · cases i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact h.goStep hop _ (go_aft_cas10 hl hpc)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [next_ret hop]
      obtain ⟨hls, -, hw, -⟩ := hb2 rfl
      exact h.fret hop ho hopr' hls (hw rfl)
  · simp only [↓reduceIte]
    rw [next_ret hop]
    exact ⟨_, h.done_noL hop ho hpw _ ⟨rfl, rfl, by intros; simp⟩
      (fun id resp d he => by simp only [Ev.ret.injEq] at he; exact ⟨he.2.1.symm, hb1 rfl⟩)⟩

theorem step_aft_wr15 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {b : Bool} {w : Cell V}
    (hpc : (a.ps p).pc = .aft (.wr15 w) b) : ∃ g', GInv init (apstep a p) g' := by
  simp only [apstep, hop, hpc, afterCall]
  exact h.goStep hop _ (go_aft_wr15 (h.loc p r hop) hpc)

theorem step_aft_tw21 {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {ret : Ret V} {zh wh : Cell V} {b : Bool}
    (hpc : (a.ps p).pc = .aft (.tw21 ret zh wh) b) : ∃ g', GInv init (apstep a p) g' := by
  have hl := h.loc p r hop
  obtain ⟨-, hm⟩ := h.pcok hop hpc
  simp only [apstep, hop, hpc, afterCall]
  rcases ret with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only [afterTW, Stage] at hm ⊢
  · exact h.goStep hop _ (go_aft_tw21_casT hl hpc)
  · have := go_aft_tw21_1 hl hpc (Or.inl rfl)
    rw [if_pos rfl] at this
    exact h.goStep hop _ this
  · exact h.wretStep hop hpc (by simp) hm.1 (hm.2.1 trivial)
  · have := go_aft_tw21_1 hl hpc (Or.inr rfl)
    rw [if_neg (by simp)] at this
    exact h.goStep hop _ this
  · exact h.rdoneStep hop hpc (by simp) (hm.1 trivial)

end Podc.DuraCAS
