import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolBack

/-!
# Forward simulation: machine steps are simulated by protocol paths

* `exec_pi`: from `π(C)`, a machine step `C → C'` is simulated by a path to `π(C')`.
* `rep_complete`: from any clean configuration representing `C`, the protocol can finish the
  instruction in progress, reaching `π(C₁)` for some `C →* C₁` — unless it waits for a move from an
  empty register (`Hung`), in which case the machine hangs as well.
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-- Reachability in the protocol `PP` (before the output broadcast). -/
abbrev PReach : Multiset (St Q F) → Multiset (St Q F) → Prop := Reach A.basePP.Step

theorem preach_of_fires {t : Transition (St Q F)} (ht : A.Tr t) {c c' : Multiset (St Q F)}
    (hf : t.Fires c c') : A.PReach c c' := .single (.inr ⟨t, ht, hf⟩)

theorem preach_head {t : Transition (St Q F)} (ht : A.Tr t) {c c' c'' : Multiset (St Q F)}
    (hf : t.Fires c c') (h : A.PReach c' c'') : A.PReach c c'' :=
  Relation.ReflTransGen.head (.inr ⟨t, ht, hf⟩) h

theorem dom_V_of_wf {C : Cfg Q F} (hw : A.WF C) (x : Option Q) : C.ptr (A.V x) ∈ A.dom (A.V x) := by
  have := hw (A.V x); rwa [A.dom'_of_ne (A.V_ne_IP x)] at this

section chains

variable {C : Cfg Q F} {i : ℕ}

theorem chain_mvFin {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w) :
    A.PReach (render C.reg (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .done)))
      (pi C) :=
  A.preach_of_fires (.mvEnd hI (hw' ▸ A.dom_V_of_wf hw _)) (A.fire_mvEnd hi hw')

theorem chain_mvTake {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w)
    (hpos : 0 < C.reg w) :
    A.PReach (render (mvR C.reg w A.z0)
      (A.gW C i (A.V (some y)) (.ptr (A.V (some y)) (.reg w) .take))) (pi C) :=
  A.preach_head (.mvPut hI (hw' ▸ A.dom_V_of_wf hw _)) (A.fire_mvPut hpos)
    (A.chain_mvFin hw hi hI hw')

theorem chain_mvHalf {x y w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hw' : C.ptr (A.V (some y)) = .reg w)
    (hpos : 0 < C.reg w) :
    A.PReach (render (mvR C.reg w A.z0) (A.gH C i)) (pi C) :=
  A.preach_head (.mvTake (s := .none) hI (hw' ▸ A.dom_V_of_wf hw _)) (A.fire_mvTake hw')
    (A.chain_mvTake hw hi hI hw' hpos)

theorem chain_mvDone {x y u w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.move x y)) (hu : C.ptr (A.V (some x)) = .reg u)
    (hw' : C.ptr (A.V (some y)) = .reg w) (hpos : 0 < C.reg w) :
    A.PReach (render (mvR C.reg w A.z0)
      (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done))) (pi C) :=
  A.preach_head (.mvHalf hI (hu ▸ A.dom_V_of_wf hw _)) (A.fire_mvHalf hu)
    (A.chain_mvHalf hw hi hI hw' hpos)

/-- From the start of a move with a nonempty source register, the protocol completes the move. -/
theorem chain_mvEmit {x y u w : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
    (hI : A.instr i = some (.move x y)) (hu : C.ptr (A.V (some x)) = .reg u)
    (hw' : C.ptr (A.V (some y)) = .reg w) (hpos : 0 < C.reg u) :
    A.PReach (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .emit)))
      (pi ⟨mvR C.reg u w, Function.update C.ptr A.IP (.nat (i + 1))⟩) := by
  have hE := Exec.move hi hI hu hw' hpos
  exact A.preach_head (.mvEmit hI (hu ▸ A.dom_V_of_wf hw _)) (A.fire_mvEmit hi hu hpos w)
    (A.chain_mvDone (A.exec_wf hw hE) (by simp) hI (by simp [hu]) (by simp [hw']) pos_mvR)

theorem chain_tsFin {x u : Q} (hw : A.WF C) (hi : C.ptr A.IP = .nat (i + 1))
    (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u) :
    A.PReach (render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .done)))
      (pi C) :=
  A.preach_of_fires (.tsEnd hI (hu ▸ A.dom_V_of_wf hw _)) (A.fire_tsEnd hi hu)

theorem chain_tsRes {x u : Q} (b : Bool) (hw : A.WF C) (hi : C.ptr A.IP = .nat i)
    (hI : A.instr i = some (.detect x)) (hu : C.ptr (A.V (some x)) = .reg u)
    (hb : b = false ∨ b = decide (0 < C.reg u)) :
    A.PReach (render C.reg (A.gW C i (A.V (some x))
      (.ptr (A.V (some x)) (.reg u) (if b then .tt else .ff))))
      (pi ⟨C.reg, Function.update (Function.update C.ptr A.CF (.bool b)) A.IP (.nat (i + 1))⟩) := by
  have hE := Exec.detect hi hI hu b hb
  exact A.preach_head (.tsSet (s := .none) b hI (hu ▸ A.dom_V_of_wf hw _)) (A.fire_tsSet hi b)
    (A.chain_tsFin (A.exec_wf hw hE) (by simp) hI (by simp [hu]))

theorem chain_asFin {X Y : F} {f : Val Q → Val Q} (hw : A.WF C)
    (hi : C.ptr A.IP = .nat (i + 1)) (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y)
    (hX : X ≠ A.IP) (hY : Y ≠ A.IP) :
    A.PReach (render C.reg (A.gW C i X (.ptr X (C.ptr X) .done))) (pi C) := by
  have hv : C.ptr X ∈ A.dom X := by have := hw X; rwa [A.dom'_of_ne hX] at this
  exact A.preach_of_fires (.asEnd hI hXY hX hY hv) (A.fire_asEnd hi hX)

theorem chain_asMap {X Y : F} {f : Val Q → Val Q} (hw : A.WF C)
    (hi : C.ptr A.IP = .nat i) (hI : A.instr i = some (.assign X Y f)) (hXY : X ≠ Y)
    (hX : X ≠ A.IP) (hY : Y ≠ A.IP) :
    A.PReach (render C.reg (A.gW C i X (.map X i)))
      (pi ⟨C.reg, Function.update (Function.update C.ptr X (f (C.ptr Y))) A.IP
        (.nat (i + 1))⟩) := by
  have hv : C.ptr Y ∈ A.dom Y := by have := hw Y; rwa [A.dom'_of_ne hY] at this
  have hE := Exec.assign hi hI hX
  refine A.preach_head (.asMap hI hXY hX hY hv) (A.fire_asMap hXY hX hY) ?_
  have := A.chain_asFin (A.exec_wf hw hE) (by simp) hI hXY hX hY
  convert this using 4
  simp [Function.update_of_ne hX]

end chains

/-- **Forward simulation** of one machine step from `π(C)`. -/
theorem exec_pi {C C' : Cfg Q F} (hw : A.WF C) (h : A.Exec C C') : A.PReach (pi C) (pi C') := by
  cases h with
  | @move i x y u w hi hI hu hw' hpos =>
    exact A.preach_head (.mvStart (s := .none) hI (hu ▸ A.dom_V_of_wf hw _))
      (A.fire_mvStart hi hu) (A.chain_mvEmit hw hi hI hu hw' hpos)
  | @detect i x u hi hI hu b hb =>
    refine A.preach_head (.tsStart (s := .none) hI (hu ▸ A.dom_V_of_wf hw _))
      (A.fire_tsStart hi hu) ?_
    cases b
    · exact A.preach_head (.tsNo hI (hu ▸ A.dom_V_of_wf hw _) (by simp)) A.fire_tsNo
        (A.chain_tsRes false hw hi hI hu hb)
    · have hpos : 0 < C.reg u := by
        rcases hb with h | h
        · simp at h
        · simpa using h.symm
      exact A.preach_head (.tsYes hI (hu ▸ A.dom_V_of_wf hw _)) (A.fire_tsYes hpos)
        (A.chain_tsRes true hw hi hI hu hb)
  | @assign i X Y f hi hI hX =>
    by_cases hY : Y = A.IP
    · subst hY
      have := A.preach_of_fires (.asIP (v := C.ptr X) (s := .none) hI hX) (A.fire_asIP hi hX)
      rwa [hi] at this ⊢
    by_cases hXY : X = Y
    · subst hXY
      have hv : C.ptr X ∈ A.dom X := by have := hw X; rwa [A.dom'_of_ne hX] at this
      exact A.preach_of_fires (.asSelf (s := .none) hI hX hv) (A.fire_asSelf hi hX)
    · exact A.preach_head (.asStart (v := C.ptr X) (s := .none) hI hXY hX hY)
        (A.fire_asStart hi hX) (A.chain_asMap hw hi hI hXY hX hY)
  | @jump i Y f hi hI =>
    by_cases hY : Y = A.IP
    · subst hY
      exact A.preach_of_fires (.jmpIP hI) (A.fire_jmpIP hi)
    · have hv : C.ptr Y ∈ A.dom Y := by have := hw Y; rwa [A.dom'_of_ne hY] at this
      exact A.preach_of_fires (.jmp (s := .none) hI hY hv) (A.fire_jmp hi hY)

/-- The protocol waits for a move from an empty register; the machine hangs. -/
def Hung (d : Multiset (St Q F)) (C : Cfg Q F) : Prop :=
  ∃ i x y u, C.ptr A.IP = .nat i ∧ A.instr i = some (.move x y) ∧
    C.ptr (A.V (some x)) = .reg u ∧ C.reg u = 0 ∧
    d = render C.reg (A.gW C i (A.V (some x)) (.ptr (A.V (some x)) (.reg u) .emit))

theorem hung_no_exec {d : Multiset (St Q F)} {C C' : Cfg Q F} (h : A.Hung d C) :
    ¬ A.Exec C C' := by
  obtain ⟨i, x, y, u, hi, hI, hu, h0, -⟩ := h
  intro hE
  cases hE with
  | move hi' hI' hu' hw' hpos =>
    rw [hi] at hi'; cases hi'
    rw [hI] at hI'; simp only [Option.some.injEq, MInstr.move.injEq] at hI'
    obtain ⟨rfl, rfl⟩ := hI'
    rw [hu] at hu'; cases hu'; omega
  | detect hi' hI' => rw [hi] at hi'; cases hi'; rw [hI] at hI'; simp at hI'
  | assign hi' hI' => rw [hi] at hi'; cases hi'; rw [hI] at hI'; simp at hI'
  | jump hi' hI' => rw [hi] at hi'; cases hi'; rw [hI] at hI'; simp at hI'

/-- `d` is `π(C)` or waits for a move from an empty register. -/
def Settled (d : Multiset (St Q F)) (C : Cfg Q F) : Prop := A.WF C ∧ (d = pi C ∨ A.Hung d C)

theorem settled_reach {d : Multiset (St Q F)} {C C' : Cfg Q F} (h : A.Settled d C)
    (hr : Reach A.Step C C') : ∃ d', A.PReach d d' ∧ A.Settled d' C' := by
  induction hr with
  | refl => exact ⟨d, .refl, h⟩
  | tail _ hs ih =>
    obtain ⟨d₁, h₁, hw, hd⟩ := ih
    rcases hs with hE | ⟨rfl, -⟩
    · rcases hd with rfl | hH
      · exact ⟨_, h₁.trans (A.exec_pi hw hE), A.exec_wf hw hE, .inl rfl⟩
      · exact absurd hE (A.hung_no_exec hH)
    · exact ⟨d₁, h₁, hw, hd⟩

/-- Completion of the instruction in progress. -/
theorem rep_complete {c : Multiset (St Q F)} {C : Cfg Q F} (h : A.Rep c C) :
    ∃ C₁ d, Reach A.Step C C₁ ∧ A.PReach c d ∧ A.Settled d C₁ := by
  cases h with
  | idle hw => exact ⟨C, _, .refl, .refl, hw, .inl rfl⟩
  | @mvEmit C i x y u hw hi hI hu =>
    by_cases h0 : C.reg u = 0
    · exact ⟨C, _, .refl, .refl, hw, .inr ⟨i, x, y, u, hi, hI, hu, h0, rfl⟩⟩
    · obtain ⟨w, hw'⟩ := A.ptr_V_reg hw (some y)
      have hE := Exec.move hi hI hu hw' (Nat.pos_of_ne_zero h0)
      exact ⟨_, _, .single (.inl hE), A.chain_mvEmit hw hi hI hu hw' (Nat.pos_of_ne_zero h0),
        A.exec_wf hw hE, .inl rfl⟩
  | mvDone hw hi hI hu hw' hpos =>
    exact ⟨C, _, .refl, A.chain_mvDone hw hi hI hu hw' hpos, hw, .inl rfl⟩
  | mvHalf hw hi hI hw' hpos =>
    exact ⟨C, _, .refl, A.chain_mvHalf hw hi hI hw' hpos, hw, .inl rfl⟩
  | mvTake hw hi hI hw' hpos =>
    exact ⟨C, _, .refl, A.chain_mvTake hw hi hI hw' hpos, hw, .inl rfl⟩
  | mvFin hw hi hI hw' => exact ⟨C, _, .refl, A.chain_mvFin hw hi hI hw', hw, .inl rfl⟩
  | @tsTest C i x u hw hi hI hu =>
    have hE := Exec.detect hi hI hu false (.inl rfl)
    exact ⟨_, _, .single (.inl hE),
      A.preach_head (.tsNo hI (hu ▸ A.dom_V_of_wf hw _) (by simp)) A.fire_tsNo
        (A.chain_tsRes false hw hi hI hu (.inl rfl)), A.exec_wf hw hE, .inl rfl⟩
  | @tsRes C i x u b hw hi hI hu hb =>
    have hb' : b = false ∨ b = decide (0 < C.reg u) := by
      cases b
      · exact .inl rfl
      · exact .inr (by simp [hb rfl])
    have hE := Exec.detect hi hI hu b hb'
    exact ⟨_, _, .single (.inl hE), A.chain_tsRes b hw hi hI hu hb', A.exec_wf hw hE, .inl rfl⟩
  | tsFin hw hi hI hu => exact ⟨C, _, .refl, A.chain_tsFin hw hi hI hu, hw, .inl rfl⟩
  | asMap hw hi hI hXY hX hY =>
    have hE := Exec.assign hi hI hX
    exact ⟨_, _, .single (.inl hE), A.chain_asMap hw hi hI hXY hX hY, A.exec_wf hw hE, .inl rfl⟩
  | asFin hw hi hI hXY hX hY => exact ⟨C, _, .refl, A.chain_asFin hw hi hI hXY hX hY, hw, .inl rfl⟩

end Machine

end Podc.PPDoubleExpThresholds
