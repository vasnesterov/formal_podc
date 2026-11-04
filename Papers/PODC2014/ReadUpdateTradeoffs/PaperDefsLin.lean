import Papers.PODC2014.ReadUpdateTradeoffs.PaperDefs
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# The toy max register is linearizable and wait-free

`toyImpl` (a single-writer max register from one read/write/CAS register, whose `WriteMax`
writes the writer's running maximum **twice**) is a genuine implementation of the max register
`maxRegObj`: it is linearizable (`toyImpl_linearizable`) and wait-free (`toyImpl_waitFree`). So
the counterexamples `lemma2_false` and `claim1_false` live in a correct implementation.

Linearization points: `WriteMax` at its first write, `ReadMax` at its read. The invariant `Inv`
carries a linearization `L` of the execution with `linState L` equal to the register's value.
-/

namespace Podc.ReadUpdateTradeoffs.PaperDefs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

/-- The response of an already linearized operation (`none`: not linearized or idle). -/
def Loc.linResp : Loc → Option ℕ
  | .w₂ _ | .done _ => some 0
  | .rdone _ v => some v
  | _ => none

/-- A pending operation that is not linearized yet. -/
def Loc.Unlin : Loc → Prop
  | .w₁ _ | .rd _ => True
  | _ => False

/-- The idle local state. -/
def Loc.IsIdle : Loc → Prop
  | .idle _ => True
  | _ => False

/-- A local state of a `WriteMax` operation. -/
def Loc.IsWr : Loc → Prop
  | .w₁ _ | .w₂ _ | .done _ => True
  | _ => False

/-- Before the first write of a `WriteMax`. -/
def Loc.IsW₁ : Loc → Prop
  | .w₁ _ => True
  | _ => False

/-- The number of base-object accesses the current operation still has to perform. -/
def Loc.taus : Loc → ℕ
  | .w₁ _ => 2
  | .w₂ _ | .rd _ => 1
  | _ => 0

/-- The local state after invoking `o` from `idle m`. -/
def invLoc (m : ℕ) : maxRegObj.Op → Loc
  | .writeMax v => .w₁ (max m v)
  | .readMax => .rd m

/-- The linearizability invariant of `toyImpl`. -/
structure Inv (α : List (Label (Fin 2) maxRegObj))
    (C : Config maxRegObj (RWC Unit ℕ 0) (Fin 2) Loc)
    (L : List (OpId (Fin 2) × maxRegObj.Op)) : Prop where
  lin : IsLinearization α L
  mem : C.mem () = linState L
  idle : ∀ p, C.pend p = none ↔ (C.loc p).IsIdle
  wr : ∀ p, (C.loc p).IsWr → p = 0
  w₁ : ∀ p m, C.loc p = .w₁ m → ∃ v, C.pend p = some (.writeMax v) ∧ m = max (C.mem ()) v
  mx : ¬ (C.loc 0).IsW₁ → (C.loc 0).mx = C.mem ()
  rd : ∀ p m, C.loc p = .rd m → C.pend p = some .readMax
  unlin : ∀ p, (C.loc p).Unlin → curOp α p ∉ L.map Prod.fst
  done : ∀ p r, (C.loc p).linResp = some r → ∃ L₁ L₂ o,
    L = L₁ ++ (curOp α p, o) :: L₂ ∧
    (maxRegObj.δ (maxRegObj.runOps maxRegObj.init (L₁.map Prod.snd)) o).2 = r

lemma inv_init : Inv [] toyImpl.initCfg [] := by
  refine ⟨⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
    fun a b _ hb => by simp at hb, trivial⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [toyImpl, Impl.initCfg, Loc.IsIdle, Loc.IsWr, Loc.IsW₁, Loc.Unlin, Loc.linResp, Loc.mx]

section Steps

variable {α : List (Label (Fin 2) maxRegObj)} {C C' : Config maxRegObj (RWC Unit ℕ 0) (Fin 2) Loc}
  {L : List (OpId (Fin 2) × maxRegObj.Op)} {p : Fin 2}

lemma inv_step_inv {o : maxRegObj.Op} (hrun : toyImpl.run α = some C) (hI : Inv α C L)
    (hs : toyImpl.step C (.inv p o) = some C') : Inv (α ++ [.inv p o]) C' L := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hs
  obtain ⟨m, hm⟩ : ∃ m, C.loc p = .idle m := by
    have := (hI.idle p).1 h0
    cases h : C.loc p <;> simp_all [Loc.IsIdle]
  have hnot : curOp α p ∉ L.map Prod.fst := fun h =>
    toyImpl.not_invoked_curOp_of_idle hrun h0 (hI.lin.mem_invoked h)
  have hmem' : C'.mem () = C.mem () := by rw [hmem]
  have hnew : C'.loc p = invLoc m o := by
    rw [hloc, Function.update_self, hm]; cases o <;> rfl
  have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q ∧ C'.pend q = C.pend q := fun q hq => by
    rw [hloc, hpend, Function.update_of_ne hq, Function.update_of_ne hq]; exact ⟨rfl, rfl⟩
  have hpp : C'.pend p = some o := by rw [hpend, Function.update_self]
  have hcur : ∀ q, curOp (α ++ [.inv p o]) q = curOp α q := fun q => curOp_append_inv α p q o
  refine ⟨hI.lin.append_inv p o, by rw [hmem', hI.mem], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = p
    · subst hq; rw [hpp, hnew]; cases o <;> simp [Loc.IsIdle, invLoc]
    · rw [(hoth q hq).1, (hoth q hq).2]; exact hI.idle q
  · intro q hw
    by_cases hq : q = p
    · subst hq; rw [hnew] at hw
      cases o with
      | writeMax v => exact hal v rfl
      | readMax => simp [invLoc, Loc.IsWr] at hw
    · rw [(hoth q hq).1] at hw; exact hI.wr q hw
  · intro q m' hq'
    by_cases hq : q = p
    · subst hq; rw [hnew] at hq'
      cases o with
      | writeMax v =>
        simp only [invLoc, Loc.w₁.injEq] at hq'
        refine ⟨v, hpp, ?_⟩
        have hq0 := hal v rfl; subst hq0
        have := hI.mx (by simp [hm, Loc.IsW₁]); rw [hm] at this; simp only [Loc.mx] at this
        rw [hmem', ← hq', this]
      | readMax => simp [invLoc] at hq'
    · rw [(hoth q hq).1] at hq'
      obtain ⟨v, h1, h2⟩ := hI.w₁ q m' hq'
      exact ⟨v, by rw [(hoth q hq).2]; exact h1, by rw [hmem']; exact h2⟩
  · intro hn
    rw [hmem']
    by_cases hq : (0 : Fin 2) = p
    · subst hq
      have := hI.mx (by simp [hm, Loc.IsW₁]); rw [hm] at this
      rw [hnew] at hn ⊢
      cases o with
      | writeMax v => simp [invLoc, Loc.IsW₁] at hn
      | readMax => simpa [invLoc, Loc.mx] using this
    · rw [(hoth 0 hq).1] at hn ⊢; exact hI.mx hn
  · intro q m' hq'
    by_cases hq : q = p
    · subst hq; rw [hnew] at hq'
      cases o with
      | writeMax v => simp [invLoc] at hq'
      | readMax => exact hpp
    · rw [(hoth q hq).1] at hq'; rw [(hoth q hq).2]; exact hI.rd q m' hq'
  · intro q hu
    rw [hcur]
    by_cases hq : q = p
    · subst hq; exact hnot
    · rw [(hoth q hq).1] at hu; exact hI.unlin q hu
  · intro q r hr
    rw [hcur]
    by_cases hq : q = p
    · subst hq; rw [hnew] at hr; cases o <;> simp [invLoc, Loc.linResp] at hr
    · rw [(hoth q hq).1] at hr; exact hI.done q r hr

lemma inv_step_ret {r : ℕ} (hI : Inv α C L)
    (hs : toyImpl.step C (.ret p r) = some C') : Inv (α ++ [.ret p r]) C' L := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q ∧ C'.pend q = C.pend q := fun q hq => by
    rw [hloc, hpend, Function.update_of_ne hq, Function.update_of_ne hq]; exact ⟨rfl, rfl⟩
  have hcur : ∀ q, q ≠ p → curOp (α ++ [.ret p r]) q = curOp α q := fun q hq =>
    curOp_append_ret_of_ne α r (Ne.symm hq)
  have hmem' : C'.mem () = C.mem () := by rw [hmem]
  have hpp : C'.pend p = none := by rw [hpend, Function.update_self]
  obtain ⟨m, rfl, hlr, hw1, hmx⟩ : ∃ m, l = .idle m ∧ (C.loc p).linResp = some r ∧
      ¬ (C.loc p).IsW₁ ∧ (C.loc p).mx = m := by
    cases hl : C.loc p with
    | idle m => exact absurd ((hI.idle p).2 (by simp [hl, Loc.IsIdle])) h0
    | w₁ _ => simp [toyImpl, hl] at hact
    | w₂ _ => simp [toyImpl, hl] at hact
    | rd _ => simp [toyImpl, hl] at hact
    | done m =>
      simp only [toyImpl, hl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      exact ⟨m, rfl, by simp [Loc.linResp], by simp [Loc.IsW₁], rfl⟩
    | rdone m v =>
      simp only [toyImpl, hl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      exact ⟨m, rfl, by simp [Loc.linResp], by simp [Loc.IsW₁], rfl⟩
  have hnew : C'.loc p = .idle m := by rw [hloc, Function.update_self]
  obtain ⟨L₁, L₂, o, hsplit, hr⟩ := hI.done p r hlr
  refine ⟨hI.lin.append_ret L₁ L₂ o hsplit hr, by rw [hmem', hI.mem], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = p
    · subst hq; simp [hpp, hnew, Loc.IsIdle]
    · rw [(hoth q hq).1, (hoth q hq).2]; exact hI.idle q
  · intro q hw
    by_cases hq : q = p
    · subst hq; simp [hnew, Loc.IsWr] at hw
    · rw [(hoth q hq).1] at hw; exact hI.wr q hw
  · intro q m' hq'
    by_cases hq : q = p
    · subst hq; simp [hnew] at hq'
    · rw [(hoth q hq).1] at hq'
      obtain ⟨v, h1, h2⟩ := hI.w₁ q m' hq'
      exact ⟨v, by rw [(hoth q hq).2]; exact h1, by rw [hmem']; exact h2⟩
  · intro hn
    rw [hmem']
    by_cases hq : (0 : Fin 2) = p
    · subst hq; rw [hnew]; simp only [Loc.mx]; rw [← hmx]; exact hI.mx hw1
    · rw [(hoth 0 hq).1] at hn ⊢; exact hI.mx hn
  · intro q m' hq'
    by_cases hq : q = p
    · subst hq; simp [hnew] at hq'
    · rw [(hoth q hq).1] at hq'; rw [(hoth q hq).2]; exact hI.rd q m' hq'
  · intro q hu
    by_cases hq : q = p
    · subst hq; simp [hnew, Loc.Unlin] at hu
    · rw [hcur q hq]; rw [(hoth q hq).1] at hu; exact hI.unlin q hu
  · intro q r' hr'
    by_cases hq : q = p
    · subst hq; simp [hnew, Loc.linResp] at hr'
    · rw [hcur q hq]; rw [(hoth q hq).1] at hr'; exact hI.done q r' hr'

lemma inv_step_tau (hrun : toyImpl.run α = some C) (hI : Inv α C L)
    (hs : toyImpl.step C (.tau p) = some C') : ∃ L', Inv (α ++ [.tau p]) C' L' := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  cases i
  have hoth : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hcur : ∀ q, curOp (α ++ [.tau p]) q = curOp α q := fun q => curOp_append_tau α p q
  cases hl : C.loc p with
  | idle m => simp [toyImpl, hl] at hact
  | done m => simp [toyImpl, hl] at hact
  | rdone m v => simp [toyImpl, hl] at hact
  | w₁ m =>
    have hp0 : p = 0 := hI.wr p (by simp [hl, Loc.IsWr])
    subst hp0
    obtain ⟨v, hpv, hmv⟩ := hI.w₁ 0 m hl
    simp only [toyImpl, hl, Action.access.injEq, true_and] at hact
    obtain ⟨h1, h2⟩ := hact
    have ho : o = .write m := (eq_of_heq h1).symm
    have hk : k = fun _ => Loc.w₂ m := (eq_of_heq h2).symm
    subst ho hk
    have hm' : C'.mem () = m := by rw [hmem]; simp
    have hnew : C'.loc 0 = .w₂ m := by rw [hloc, Function.update_self]
    obtain ⟨-, hnc, hop⟩ := toyImpl.run_pend_curOp hrun hpv
    have hnot := hI.unlin 0 (by simp [hl, Loc.Unlin])
    refine ⟨L ++ [(curOp α 0, .writeMax v)], (hI.lin.push hop hnot hnc).append_tau 0, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm', hmv, hI.mem]; simp only [linState, List.map_append, List.map_cons, List.map_nil]
      rw [ObjSpec.runOps_append]; rfl
    · intro q
      by_cases hq : q = 0
      · subst hq; simp [hpend, hpv, hnew, Loc.IsIdle]
      · rw [hpend, hoth q hq]; exact hI.idle q
    · intro q hw
      by_cases hq : q = 0
      · exact hq
      · rw [hoth q hq] at hw; exact hI.wr q hw
    · intro q m' hq'
      by_cases hq : q = 0
      · subst hq; simp [hnew] at hq'
      · rw [hoth q hq] at hq'; exact absurd (hI.wr q (by simp [hq', Loc.IsWr])) hq
    · intro _; simp [hnew, Loc.mx, hm']
    · intro q m' hq'
      by_cases hq : q = 0
      · subst hq; simp [hnew] at hq'
      · rw [hoth q hq] at hq'; rw [hpend]; exact hI.rd q m' hq'
    · intro q hu
      rw [hcur]
      by_cases hq : q = 0
      · subst hq; simp [hnew, Loc.Unlin] at hu
      · rw [hoth q hq] at hu
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, not_or]
        exact ⟨hI.unlin q hu, fun h => hq (congrArg Prod.fst h)⟩
    · intro q r hr
      rw [hcur]
      by_cases hq : q = 0
      · subst hq
        simp only [hnew, Loc.linResp, Option.some.injEq] at hr
        exact ⟨L, [], .writeMax v, by simp, by simp [← hr]⟩
      · rw [hoth q hq] at hr
        obtain ⟨L₁, L₂, o, hsp, hr'⟩ := hI.done q r hr
        exact ⟨L₁, L₂ ++ [(curOp α 0, .writeMax v)], o, by simp [hsp], hr'⟩
  | w₂ m =>
    have hp0 : p = 0 := hI.wr p (by simp [hl, Loc.IsWr])
    subst hp0
    have hmx : m = C.mem () := by
      have := hI.mx (by simp [hl, Loc.IsW₁]); rwa [hl] at this
    simp only [toyImpl, hl, Action.access.injEq, true_and] at hact
    obtain ⟨h1, h2⟩ := hact
    have ho : o = .write m := (eq_of_heq h1).symm
    have hk : k = fun _ => Loc.done m := (eq_of_heq h2).symm
    subst ho hk
    have hm' : C'.mem () = C.mem () := by rw [hmem]; simp [hmx]
    have hnew : C'.loc 0 = .done m := by rw [hloc, Function.update_self]
    refine ⟨L, hI.lin.append_tau 0, by rw [hm', hI.mem], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q
      by_cases hq : q = 0
      · subst hq
        have : C.pend 0 ≠ none := h0
        simp [hpend, this, hnew, Loc.IsIdle]
      · rw [hpend, hoth q hq]; exact hI.idle q
    · intro q hw
      by_cases hq : q = 0
      · exact hq
      · rw [hoth q hq] at hw; exact hI.wr q hw
    · intro q m' hq'
      by_cases hq : q = 0
      · subst hq; simp [hnew] at hq'
      · rw [hoth q hq] at hq'; exact absurd (hI.wr q (by simp [hq', Loc.IsWr])) hq
    · intro _; simp [hnew, Loc.mx, hm', hmx]
    · intro q m' hq'
      by_cases hq : q = 0
      · subst hq; simp [hnew] at hq'
      · rw [hoth q hq] at hq'; rw [hpend]; exact hI.rd q m' hq'
    · intro q hu
      rw [hcur]
      by_cases hq : q = 0
      · subst hq; simp [hnew, Loc.Unlin] at hu
      · rw [hoth q hq] at hu; exact hI.unlin q hu
    · intro q r hr
      rw [hcur]
      by_cases hq : q = 0
      · subst hq
        simp only [hnew, Loc.linResp] at hr
        exact hI.done 0 r (by simp [hl, Loc.linResp, hr])
      · rw [hoth q hq] at hr; exact hI.done q r hr
  | rd m =>
    have hpr := hI.rd p m hl
    simp only [toyImpl, hl, Action.access.injEq, true_and] at hact
    obtain ⟨h1, h2⟩ := hact
    have ho : o = .read := (eq_of_heq h1).symm
    have hk : k = fun x => Loc.rdone m (x.elim id (fun _ => 0)) := (eq_of_heq h2).symm
    subst ho hk
    have hm' : C'.mem () = C.mem () := by rw [hmem]; simp
    have hnew : C'.loc p = .rdone m (C.mem ()) := by rw [hloc, Function.update_self]; rfl
    obtain ⟨-, hnc, hop⟩ := toyImpl.run_pend_curOp hrun hpr
    have hnot := hI.unlin p (by simp [hl, Loc.Unlin])
    refine ⟨L ++ [(curOp α p, .readMax)], (hI.lin.push hop hnot hnc).append_tau p, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm', hI.mem]; simp only [linState, List.map_append, List.map_cons, List.map_nil]
      rw [ObjSpec.runOps_append]; rfl
    · intro q
      by_cases hq : q = p
      · subst hq; simp [hpend, hpr, hnew, Loc.IsIdle]
      · rw [hpend, hoth q hq]; exact hI.idle q
    · intro q hw
      by_cases hq : q = p
      · subst hq; simp [hnew, Loc.IsWr] at hw
      · rw [hoth q hq] at hw; exact hI.wr q hw
    · intro q m' hq'
      by_cases hq : q = p
      · subst hq; simp [hnew] at hq'
      · rw [hoth q hq] at hq'
        obtain ⟨v, h1, h2⟩ := hI.w₁ q m' hq'
        exact ⟨v, by rw [hpend]; exact h1, by rw [hm']; exact h2⟩
    · intro hn
      rw [hm']
      by_cases hq : (0 : Fin 2) = p
      · subst hq
        have := hI.mx (by simp [hl, Loc.IsW₁]); rw [hl] at this
        simpa [hnew, Loc.mx] using this
      · rw [hoth 0 hq] at hn ⊢; exact hI.mx hn
    · intro q m' hq'
      by_cases hq : q = p
      · subst hq; simp [hnew] at hq'
      · rw [hoth q hq] at hq'; rw [hpend]; exact hI.rd q m' hq'
    · intro q hu
      rw [hcur]
      by_cases hq : q = p
      · subst hq; simp [hnew, Loc.Unlin] at hu
      · rw [hoth q hq] at hu
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, not_or]
        exact ⟨hI.unlin q hu, fun h => hq (congrArg Prod.fst h)⟩
    · intro q r hr
      rw [hcur]
      by_cases hq : q = p
      · subst hq
        simp only [hnew, Loc.linResp, Option.some.injEq] at hr
        refine ⟨L, [], .readMax, by simp, ?_⟩
        rw [← hr, hI.mem]; rfl
      · rw [hoth q hq] at hr
        obtain ⟨L₁, L₂, o, hsp, hr'⟩ := hI.done q r hr
        exact ⟨L₁, L₂ ++ [(curOp α p, .readMax)], o, by simp [hsp], hr'⟩

end Steps

lemma inv_of_run {α : List (Label (Fin 2) maxRegObj)}
    {C : Config maxRegObj (RWC Unit ℕ 0) (Fin 2) Loc} (h : toyImpl.run α = some C) :
    ∃ L, Inv α C L :=
  Impl.run_induction (Q := fun α C => ∃ L, Inv α C L) ⟨[], inv_init⟩
    (fun α C ℓ C' hrun ⟨L, hI⟩ hs => by
      cases ℓ with
      | inv p o => exact ⟨L, inv_step_inv hrun hI hs⟩
      | tau p => exact inv_step_tau hrun hI hs
      | ret p r => exact ⟨L, inv_step_ret hI hs⟩) h

/-- The toy single-writer max register `toyImpl` (the implementation used in `lemma2_false`
and `claim1_false`) is linearizable. -/
theorem toyImpl_linearizable : toyImpl.Linearizable :=
  Impl.linearizable_of_run fun _ _ h =>
    let ⟨L, hI⟩ := inv_of_run h
    ⟨L, hI.lin⟩

/-! ### Wait-freedom -/

lemma Loc.taus_le (l : Loc) : l.taus ≤ 2 := by cases l <;> simp [Loc.taus]

/-- While `p`'s operation is pending, every step leaves its remaining number of accesses
non-increasing, and a step of `p` decreases it. -/
lemma taus_step {C C' : Config maxRegObj (RWC Unit ℕ 0) (Fin 2) Loc}
    {ℓ : Label (Fin 2) maxRegObj} {p : Fin 2} (hs : toyImpl.step C ℓ = some C')
    (hp : C.pend p ≠ none) (hp' : C'.pend p ≠ none) :
    (C'.loc p).taus ≤ (C.loc p).taus ∧ (ℓ = .tau p → (C'.loc p).taus < (C.loc p).taus) := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (Impl.step_inv hs).1 hp
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (by rw [(Impl.step_ret hs).2.1, Function.update_self]) hp'
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
      cases i
      suffices (C'.loc q).taus < (C.loc q).taus from ⟨this.le, fun _ => this⟩
      rw [hloc, Function.update_self]
      cases hl : C.loc q with
      | idle m => simp [toyImpl, hl] at hact
      | done m => simp [toyImpl, hl] at hact
      | rdone m v => simp [toyImpl, hl] at hact
      | w₁ m =>
        simp only [toyImpl, hl, Action.access.injEq, true_and] at hact
        rw [← eq_of_heq hact.2]; simp [Loc.taus]
      | w₂ m =>
        simp only [toyImpl, hl, Action.access.injEq, true_and] at hact
        rw [← eq_of_heq hact.2]; simp [Loc.taus]
      | rd m =>
        simp only [toyImpl, hl, Action.access.injEq, true_and] at hact
        rw [← eq_of_heq hact.2]; simp [Loc.taus]
  · rw [(Impl.step_other hs hq).1]
    exact ⟨le_rfl, fun h => absurd (by rw [h]; rfl) hq⟩

/-- The toy single-writer max register `toyImpl` is wait-free: every operation performs at most
two base-object accesses. -/
theorem toyImpl_waitFree : toyImpl.WaitFree := by
  intro e p n hpend
  have hstep : ∀ m ≥ n, ((e.cfg (m + 1)).loc p).taus ≤ ((e.cfg m).loc p).taus ∧
      (e.lbl m = .tau p → ((e.cfg (m + 1)).loc p).taus < ((e.cfg m).loc p).taus) :=
    fun m hm => taus_step (e.step_eq m) (hpend m hm) (hpend (m + 1) (by omega))
  have hmono : ∀ b ≥ n, ∀ j, ((e.cfg (b + j)).loc p).taus ≤ ((e.cfg b).loc p).taus := by
    intro b hb j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ((hstep (b + j) (by omega)).1).trans ih
  by_contra hcon
  push Not at hcon
  obtain ⟨m1, hm1, ht1⟩ := hcon n
  obtain ⟨m2, hm2, ht2⟩ := hcon (m1 + 1)
  obtain ⟨m3, hm3, ht3⟩ := hcon (m2 + 1)
  have a1 := (hstep m1 hm1).2 ht1
  have a2 := (hstep m2 (by omega)).2 ht2
  have a3 := (hstep m3 (by omega)).2 ht3
  have b0 := ((e.cfg m1).loc p).taus_le
  have b1 := hmono (m1 + 1) (by omega) (m2 - (m1 + 1))
  have b2 := hmono (m2 + 1) (by omega) (m3 - (m2 + 1))
  rw [show m1 + 1 + (m2 - (m1 + 1)) = m2 by omega] at b1
  rw [show m2 + 1 + (m3 - (m2 + 1)) = m3 by omega] at b2
  omega

end Podc.ReadUpdateTradeoffs.PaperDefs
