import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Objects.TestAndSet
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.StrongLin
import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# Readable test&set from test&set (Theorem 5)

Attiya, Castañeda and Enea, PODC 2024, Section 4.1. The processes share a (non-readable)
test&set object `ts` and a read/write register `state`, initially `0` (`false`).

* `read()`: read `state` and return the value read;
* `test&set()`: `b ← ts.test&set()`, then `state.write(1)`, then return `b`.

Linearization (paper): reads at their read of `state`; let `e` be the first write of `1` to
`state` and `op*` the test&set that obtains `0` from `ts`: `op*` is linearized at `e`, followed
by all test&set operations that accessed `ts` before `e`; every other test&set is linearized at
its access to `ts`. We prove this is a forward simulation (`linSim`), hence the implementation is
strongly linearizable; it is wait-free (at most two accesses per operation).

Processes: any finite type `P` (the paper's `n`-process test&set `ts` is an ordinary test&set).
-/

namespace StrongLinCN2.RTAS

open Cslib.SharedMemory

/-- Base objects: the test&set `ts` and the register `state`. -/
inductive Obj where
  | ts
  | state
  deriving DecidableEq

/-- Specifications of the base objects. -/
abbrev B : Obj → ObjSpec
  | .ts => tasObj
  | .state => register Bool false

/-- Local states (program counters). -/
inductive Loc where
  | idle
  /-- `test&set`, about to access `ts`. -/
  | tasAcc
  /-- `test&set`, obtained `b` from `ts`, about to write `1` to `state`. -/
  | tasWr (b : Bool)
  /-- `read`, about to read `state`. -/
  | readAcc
  /-- About to return `b`. -/
  | retv (b : Bool)
  deriving DecidableEq

variable (P : Type) [DecidableEq P] [Fintype P]

/-- The implementation of Section 4.1. -/
def impl : Impl rtasObj B P Loc where
  memInit
    | .ts => false
    | .state => false
  locInit _ := .idle
  invoke _ _
    | .tas => .tasAcc
    | .read => .readAcc
  act _
    | .idle => .ret false .idle
    | .tasAcc => .access Obj.ts () (fun b => .tasWr b)
    | .tasWr b => .access Obj.state (.write true) (fun _ => .retv b)
    | .readAcc => .access Obj.state .read (fun b => .retv b)
    | .retv b => .ret b .idle

set_option linter.unusedSectionVars false

variable {P}

/-- Status of a process. -/
def St (α : List (Label P rtasObj)) (C : Config rtasObj B P Loc)
    (Lin : List (OpId P × rtasObj.Op)) (p : P) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .tasAcc => C.pend p = some .tas ∧ curOp α p ∉ Lin.map Prod.fst ∧ opOf α (curOp α p) = some .tas
  | .readAcc => C.pend p = some .read ∧ curOp α p ∉ Lin.map Prod.fst ∧
      opOf α (curOp α p) = some .read
  | .tasWr b => C.pend p = some .tas ∧ opOf α (curOp α p) = some .tas ∧ C.mem .ts = true ∧
      (C.mem .state = false → curOp α p ∉ Lin.map Prod.fst) ∧
      (C.mem .state = true → rtasObj.respIn rtasObj.init Lin (curOp α p) = some b)
  | .retv b => C.pend p ≠ none ∧ rtasObj.respIn rtasObj.init Lin (curOp α p) = some b

/-- The simulation invariant. -/
structure Inv (α : List (Label P rtasObj)) (C : Config rtasObj B P Loc)
    (Lin : List (OpId P × rtasObj.Op)) : Prop where
  lin : IsLinearization α Lin
  abs : linState Lin = C.mem .state
  wt : C.mem .state = true → C.mem .ts = true
  winner : C.mem .state = false → C.mem .ts = true → ∃ q, C.loc q = .tasWr false
  uniq : ∀ q q', C.loc q = .tasWr false → C.loc q' = .tasWr false → q = q'
  st : ∀ p, St α C Lin p

/-- Transfer of the status of a process whose local state and pending operation do not change,
when the linearization is extended without it and the relevant memory is unchanged. -/
lemma St.transfer {α α' : List (Label P rtasObj)} {C C' : Config rtasObj B P Loc}
    {Lin M : List (OpId P × rtasObj.Op)} {q : P} (h : St α C Lin q)
    (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q) (hcur : curOp α' q = curOp α q)
    (hop : ∀ o, opOf α (curOp α q) = some o → opOf α' (curOp α q) = some o)
    (hM : curOp α q ∉ M.map Prod.fst)
    (hts : C.mem .ts = true → C'.mem .ts = true) (hstate : C'.mem .state = C.mem .state) :
    St α' C' (Lin ++ M) q := by
  unfold St at h ⊢
  rw [hloc, hpend, hcur, hstate]
  have hnm : ∀ x, x ∉ Lin.map Prod.fst → x ∉ M.map Prod.fst → x ∉ (Lin ++ M).map Prod.fst := by
    intro x h1 h2; simp only [List.map_append, List.mem_append, not_or]; exact ⟨h1, h2⟩
  have hlr : ∀ b, rtasObj.respIn rtasObj.init Lin (curOp α q) = some b →
      rtasObj.respIn rtasObj.init (Lin ++ M) (curOp α q) = some b :=
    fun _ hb => ObjSpec.respIn_append_of_eq_some hb _
  split at h
  · exact h
  · exact ⟨h.1, hnm _ h.2.1 hM, hop _ h.2.2⟩
  · exact ⟨h.1, hnm _ h.2.1 hM, hop _ h.2.2⟩
  · exact ⟨h.1, hop _ h.2.1, hts h.2.2.1, fun hs => hnm _ (h.2.2.2.1 hs) hM,
      fun hs => hlr _ (h.2.2.2.2 hs)⟩
  · exact ⟨h.1, hlr _ h.2⟩

variable (P)

/-- The processes that have obtained `true` from `ts` but not yet written `state`. -/
noncomputable def losers (C : Config rtasObj B P Loc) : List P :=
  (Finset.univ.filter (fun q => C.loc q = .tasWr true)).toList

variable {P}

lemma linSim : (impl P).LinSim Inv where
  init := by
    refine ⟨isLinearization_nil, rfl, fun h => by simp [impl, Impl.initCfg] at h, ?_, ?_, ?_⟩
    · intro _ h; simp [impl, Impl.initCfg] at h
    · intro q _ h; simp [impl, Impl.initCfg] at h
    · intro p; simp [St, impl, Impl.initCfg]
  lin _ _ _ _ h := h.lin
  step := by
    intro α C Lin ℓ C' hrun hI hstep
    have hcnt := (impl P).run_counts hrun
    cases ℓ with
    | inv p o =>
      obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv hstep
      have hlen : (opsOf α p).length = (respsOf α p).length := by
        rcases hcnt p with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd h0 h1
      have hidle : C.loc p = .idle := by
        have := hI.st p
        unfold St at this
        split at this <;> simp_all
      have hnot : curOp α p ∉ Lin.map Prod.fst := by
        intro hm
        have := hI.lin.invoked_of_mem hm
        simp [Invoked] at this; omega
      have hop : opOf (α ++ [.inv p o]) (curOp α p) = some o := by
        simp [opOf, opsOf_append, ← hlen]
      have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      refine ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.abs, by rw [hmem]; exact hI.wt, ?_, ?_,
        fun q => ?_⟩
      · intro h1 h2
        rw [hmem] at h1 h2
        obtain ⟨q, hq⟩ := hI.winner h1 h2
        refine ⟨q, ?_⟩
        have hqp : q ≠ p := by rintro rfl; rw [hidle] at hq; cases hq
        rw [hlocq q hqp]; exact hq
      · intro q q' hq hq'
        have hqp : q ≠ p := by
          rintro rfl; rw [hloc, Function.update_self] at hq; cases o <;> cases hq
        have hq'p : q' ≠ p := by
          rintro rfl; rw [hloc, Function.update_self] at hq'; cases o <;> cases hq'
        exact hI.uniq q q' (by rwa [hlocq q hqp] at hq) (by rwa [hlocq q' hq'p] at hq')
      · by_cases hq : q = p
        · subst hq
          have := List.append_nil Lin
          rw [← this]
          unfold St
          rw [hloc, Function.update_self, hpend, Function.update_self, curOp_append_inv]
          cases o
          · exact ⟨rfl, by simpa using hnot, hop⟩
          · exact ⟨rfl, by simpa using hnot, hop⟩
        · have := (hI.st q).transfer (α' := α ++ [.inv p o]) (C' := C') (M := [])
            (hlocq q hq) (by rw [hpend, Function.update_of_ne hq]) (curOp_append_inv _ _ _ _)
            (fun _ h => opOf_append_of_eq_some h _) (by simp) (by rw [hmem]; exact id)
            (by rw [hmem])
          simpa using this
    | tau p =>
      obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hstep
      have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hpendq : ∀ q, C'.pend q = C.pend q := fun q => by rw [hpend]
      have hst := hI.st p
      cases hl : C.loc p with
      | idle => simp [impl, hl] at hact
      | retv b => simp [impl, hl] at hact
      | readAcc =>
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have ho' : o = RWOp.read := (eq_of_heq ho).symm
        subst ho'
        have hk' : k = fun b => Loc.retv b := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp2, hp3⟩ := hst
        have hnc : ¬ Completed α (curOp α p) := by simp [Completed]
        have hmem' : C'.mem = C.mem := by rw [hmem]; funext j; cases j <;> rfl
        refine ⟨[(curOp α p, .read)], (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, ?_, ?_, ?_,
          fun q => ?_⟩
        · rw [hmem', linState_concat]; exact hI.abs
        · rw [hmem']; exact hI.wt
        · intro h1 h2; rw [hmem'] at h1 h2
          obtain ⟨q, hq⟩ := hI.winner h1 h2
          have hqp : q ≠ p := by rintro rfl; rw [hl] at hq; cases hq
          exact ⟨q, by rw [hlocq q hqp]; exact hq⟩
        · intro q q' hq hq'
          have hqp : q ≠ p := by rintro rfl; rw [hloc, Function.update_self] at hq; cases hq
          have hq'p : q' ≠ p := by rintro rfl; rw [hloc, Function.update_self] at hq'; cases hq'
          exact hI.uniq q q' (by rwa [hlocq q hqp] at hq) (by rwa [hlocq q' hq'p] at hq')
        · by_cases hq : q = p
          · subst hq
            unfold St
            rw [hloc, Function.update_self, hpend, curOp_append_tau,
              ObjSpec.respIn_concat_self hp2]
            exact ⟨by rw [hp1]; simp, congrArg some hI.abs⟩
          · exact (hI.st q).transfer (hlocq q hq) (hpendq q) (curOp_append_tau _ _ _)
              (fun _ h => opOf_append_of_eq_some h _)
              (by simp only [List.map_cons, List.map_nil, List.mem_singleton]
                  exact fun h => hq (congrArg Prod.fst h))
              (by rw [hmem']; exact id) (by rw [hmem'])
      | tasAcc =>
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have hk' : k = fun b => Loc.tasWr b := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp2, hp3⟩ := hst
        have hnc : ¬ Completed α (curOp α p) := by simp [Completed]
        have hts' : C'.mem .ts = true := by rw [hmem]; simp
        have hstate' : C'.mem .state = C.mem .state := by rw [hmem]; simp
        have hlocp : C'.loc p = .tasWr (C.mem .ts) := by rw [hloc, Function.update_self]
        -- the uniqueness/winner facts in the new configuration
        have huniq : ∀ q q', C'.loc q = .tasWr false → C'.loc q' = .tasWr false → q = q' := by
          intro q q' hq hq'
          by_cases hqp : q = p
          · by_cases hq'p : q' = p
            · rw [hqp, hq'p]
            · exfalso
              rw [hqp, hlocp] at hq
              simp only [Loc.tasWr.injEq] at hq
              rw [hlocq q' hq'p] at hq'
              have := hI.st q'
              unfold St at this; rw [hq'] at this
              rw [hq] at this; exact absurd this.2.2.1 (by simp)
          · by_cases hq'p : q' = p
            · exfalso
              rw [hq'p, hlocp] at hq'
              simp only [Loc.tasWr.injEq] at hq'
              rw [hlocq q hqp] at hq
              have := hI.st q
              unfold St at this; rw [hq] at this
              rw [hq'] at this; exact absurd this.2.2.1 (by simp)
            · exact hI.uniq q q' (by rwa [hlocq q hqp] at hq) (by rwa [hlocq q' hq'p] at hq')
        cases hw : C.mem .state with
        | false =>
          -- not linearized yet
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          refine ⟨hI.lin.append_tau p, by rw [hstate']; exact hI.abs, ?_, ?_, huniq,
            fun q => ?_⟩
          · intro h; rw [hstate', hw] at h; cases h
          · intro _ _
            by_cases hts : C.mem .ts = true
            · obtain ⟨q, hq⟩ := hI.winner hw hts
              have hqp : q ≠ p := by rintro rfl; rw [hl] at hq; cases hq
              exact ⟨q, by rw [hlocq q hqp]; exact hq⟩
            · exact ⟨p, by rw [hlocp]; simpa using hts⟩
          · by_cases hq : q = p
            · subst hq
              unfold St
              rw [hlocp, hpend, curOp_append_tau]
              exact ⟨hp1, opOf_append_of_eq_some hp3 _, hts', fun _ => hp2,
                fun h => by rw [hstate', hw] at h; cases h⟩
            · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
                (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp)
                (fun _ => hts') hstate'
        | true =>
          -- linearized at the access to `ts`
          have hts : C.mem .ts = true := hI.wt hw
          refine ⟨[(curOp α p, .tas)], (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, ?_, ?_, huniq,
            fun q => ?_⟩
          · rw [hstate', hw, linState_concat]
          · intro _; exact hts'
          · intro h; rw [hstate', hw] at h; cases h
          · by_cases hq : q = p
            · subst hq
              unfold St
              rw [hlocp, hpend, curOp_append_tau]
              refine ⟨hp1, opOf_append_of_eq_some hp3 _, hts',
                fun h => absurd (h.symm.trans (hstate'.trans hw)) (by decide), fun _ => ?_⟩
              rw [ObjSpec.respIn_concat_self hp2, hts]
              exact congrArg (fun s => some (rtasObj.δ s .tas).2) (hI.abs.trans hw)
            · exact (hI.st q).transfer (hlocq q hq) (hpendq q) (curOp_append_tau _ _ _)
                (fun _ h => opOf_append_of_eq_some h _)
                (by simp only [List.map_cons, List.map_nil, List.mem_singleton]
                    exact fun h => hq (congrArg Prod.fst h))
                (fun _ => hts') hstate'
      | tasWr b =>
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have ho' : o = RWOp.write true := (eq_of_heq ho).symm
        subst ho'
        have hk' : k = fun _ => Loc.retv b := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp3, hpts, hpf, hpt⟩ := hst
        have hts' : C'.mem .ts = C.mem .ts := by rw [hmem]; simp
        have hstate' : C'.mem .state = true := by rw [hmem]; simp
        have hlocp : C'.loc p = .retv b := by rw [hloc, Function.update_self]
        have huniq : ∀ q q', C'.loc q = .tasWr false → C'.loc q' = .tasWr false → q = q' := by
          intro q q' hq hq'
          have hqp : q ≠ p := by rintro rfl; rw [hlocp] at hq; cases hq
          have hq'p : q' ≠ p := by rintro rfl; rw [hlocp] at hq'; cases hq'
          exact hI.uniq q q' (by rwa [hlocq q hqp] at hq) (by rwa [hlocq q' hq'p] at hq')
        cases hw : C.mem .state with
        | true =>
          -- a later write: stuttering step
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          refine ⟨hI.lin.append_tau p, by rw [hstate', ← hw]; exact hI.abs,
            fun _ => by rw [hts']; exact hpts,
            fun h => absurd (h.symm.trans hstate') (by decide), huniq, fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            unfold St
            rw [hlocp, hpend, curOp_append_tau]
            exact ⟨by rw [hp1]; simp, hpt hw⟩
          · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
              (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp)
              (fun h => by rw [hts']; exact h) (by rw [hstate', hw])
        | false =>
          -- the event `e`: linearize the winner, then all losers that accessed `ts`
          obtain ⟨w, hwin⟩ := hI.winner hw hpts
          have hwst := hI.st w
          unfold St at hwst; rw [hwin] at hwst
          obtain ⟨hw1, hw3, -, hwf, -⟩ := hwst
          let M : List (OpId P × rtasObj.Op) :=
            (curOp α w, .tas) :: (losers P C).map (fun q => (curOp α q, .tas))
          have hlos : ∀ q, q ∈ losers P C ↔ C.loc q = .tasWr true := by
            intro q; simp [losers]
          have hlosnd : (losers P C).Nodup := Finset.nodup_toList _
          have hwnot : w ∉ losers P C := by rw [hlos, hwin]; simp
          have hMfst : M.map Prod.fst = curOp α w :: (losers P C).map (curOp α) := by
            simp [M, Function.comp_def]
          have hMmem : ∀ q, curOp α q ∈ M.map Prod.fst ↔ q = w ∨ C.loc q = .tasWr true := by
            intro q
            rw [hMfst, List.mem_cons, List.mem_map]
            constructor
            · rintro (h | ⟨q', hq', h⟩)
              · exact Or.inl (congrArg Prod.fst h)
              · have : q' = q := congrArg Prod.fst h
                subst this; exact Or.inr ((hlos _).1 hq')
            · rintro (rfl | h)
              · exact Or.inl rfl
              · exact Or.inr ⟨q, (hlos _).2 h, rfl⟩
          -- statuses of the processes in `M`
          have hstW : ∀ q b', C.loc q = .tasWr b' → opOf α (curOp α q) = some .tas ∧
              ¬ Completed α (curOp α q) ∧ curOp α q ∉ Lin.map Prod.fst := by
            intro q b' hq
            have := hI.st q
            unfold St at this; rw [hq] at this
            exact ⟨this.2.1, by simp [Completed], this.2.2.2.1 hw⟩
          have hMnd : (M.map Prod.fst).Nodup := by
            rw [hMfst, List.nodup_cons]
            refine ⟨?_, hlosnd.map (fun a b h => congrArg Prod.fst h)⟩
            rw [List.mem_map]; rintro ⟨q, hq, h⟩
            have : q = w := congrArg Prod.fst h
            subst this; exact hwnot hq
          have hlinM : IsLinearization α (Lin ++ M) := by
            refine hI.lin.push_list M ?_ hMnd ?_
            · intro y hy
              simp only [M, List.mem_cons, List.mem_map] at hy
              rcases hy with rfl | ⟨q, hq, rfl⟩
              · exact ⟨(hstW w _ hwin).1, (hstW w _ hwin).2.1⟩
              · have h' := (hlos q).1 hq
                exact ⟨(hstW q _ h').1, (hstW q _ h').2.1⟩
            · intro y hy
              simp only [M, List.mem_cons, List.mem_map] at hy
              rcases hy with rfl | ⟨q, hq, rfl⟩
              · exact (hstW w _ hwin).2.2
              · exact (hstW q _ ((hlos q).1 hq)).2.2
          -- responses assigned by `Lin ++ M`
          have hLw : linState Lin = false := by rw [hI.abs, hw]
          have hrespW : rtasObj.respIn rtasObj.init (Lin ++ M) (curOp α w) = some false := by
            rw [ObjSpec.respIn_append_of_not_mem (hstW w _ hwin).2.2,
              show rtasObj.runOps rtasObj.init (Lin.map Prod.snd) = false from hLw, ObjSpec.respIn_cons_self]
          have hrespL : ∀ q, C.loc q = .tasWr true →
              rtasObj.respIn rtasObj.init (Lin ++ M) (curOp α q) = some true := by
            intro q hq
            have hqw : q ≠ w := by rintro rfl; rw [hwin] at hq; cases hq
            rw [ObjSpec.respIn_append_of_not_mem (hstW q _ hq).2.2,
              ObjSpec.respIn_cons_of_ne _ _ _ (fun h => hqw (congrArg Prod.fst h).symm)]
            -- after the winner, the state is `true`
            have hconst := ObjSpec.respIn_append_const (A := rtasObj) (q := true)
              (x := curOp α q) true (l := (losers P C).map fun q => (curOp α q, RTASOp.tas))
              (fun _ hy => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hy; rfl)
              (by rw [List.map_map]; exact List.mem_map.2 ⟨q, (hlos q).2 hq, rfl⟩) []
            rw [List.append_nil] at hconst
            exact hconst
          have hLM : linState (Lin ++ M) = true := by
            have hrun : ∀ l : List P,
                rtasObj.runOps true ((l.map (fun q => ((curOp α q, RTASOp.tas) : OpId P × _))).map
                  Prod.snd) = true := by
              intro l; induction l with
              | nil => rfl
              | cons a l ih => exact ih
            rw [linState_append]
            show rtasObj.runOps (rtasObj.δ (linState Lin) RTASOp.tas).1 _ = true
            exact hrun _
          refine ⟨M, hlinM.append_tau p, by rw [hLM, hstate'], fun _ => by rw [hts']; exact hpts,
            fun h => absurd (h.symm.trans hstate') (by decide), huniq, fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            unfold St
            rw [hlocp, hpend, curOp_append_tau]
            refine ⟨by rw [hp1]; simp, ?_⟩
            cases b with
            | false =>
              have : q = w := hI.uniq q w hl hwin
              subst this; exact hrespW
            | true => exact hrespL q hl
          · have hlq := hlocq q hq
            have hqst := hI.st q
            unfold St at hqst ⊢
            rw [hlq, hpendq q, curOp_append_tau, hstate']
            -- either `q` is in `M` (a process in `tasWr`) or it is untouched
            cases hc : C.loc q with
            | tasWr b' =>
              rw [hc] at hqst
              refine ⟨hqst.1, opOf_append_of_eq_some hqst.2.1 _, by rw [hts']; exact hqst.2.2.1,
                fun h => absurd h (by decide), fun _ => ?_⟩
              cases b' with
              | false =>
                have : q = w := hI.uniq q w hc hwin
                subst this; exact hrespW
              | true => exact hrespL q hc
            | idle => rw [hc] at hqst; exact hqst
            | tasAcc =>
              rw [hc] at hqst
              refine ⟨hqst.1, ?_, opOf_append_of_eq_some hqst.2.2 _⟩
              simp only [List.map_append, List.mem_append, not_or]
              refine ⟨hqst.2.1, fun h => ?_⟩
              rcases (hMmem q).1 h with rfl | h
              · rw [hwin] at hc; cases hc
              · rw [h] at hc; cases hc
            | readAcc =>
              rw [hc] at hqst
              refine ⟨hqst.1, ?_, opOf_append_of_eq_some hqst.2.2 _⟩
              simp only [List.map_append, List.mem_append, not_or]
              refine ⟨hqst.2.1, fun h => ?_⟩
              rcases (hMmem q).1 h with rfl | h
              · rw [hwin] at hc; cases hc
              · rw [h] at hc; cases hc
            | retv b' =>
              rw [hc] at hqst
              refine ⟨hqst.1, ?_⟩
              exact ObjSpec.respIn_append_of_eq_some hqst.2 _
    | ret p r =>
      obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
      have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hst := hI.st p
      cases hl : C.loc p with
      | idle => unfold St at hst; rw [hl] at hst; exact absurd hst h0
      | tasAcc => simp [impl, hl] at hact
      | tasWr b => simp [impl, hl] at hact
      | readAcc => simp [impl, hl] at hact
      | retv b =>
        simp only [impl, hl, Action.ret.injEq] at hact
        obtain ⟨rfl, rfl⟩ := hact
        unfold St at hst; rw [hl] at hst
        refine ⟨[], ?_⟩
        rw [List.append_nil]
        refine ⟨hI.lin.append_ret_of_respIn hst.2, by rw [hmem]; exact hI.abs,
          by rw [hmem]; exact hI.wt, ?_, ?_, fun q => ?_⟩
        · intro h1 h2; rw [hmem] at h1 h2
          obtain ⟨q, hq⟩ := hI.winner h1 h2
          have hqp : q ≠ p := by rintro rfl; rw [hl] at hq; cases hq
          exact ⟨q, by rw [hlocq q hqp]; exact hq⟩
        · intro q q' hq hq'
          have hqp : q ≠ p := by rintro rfl; rw [hloc, Function.update_self] at hq; cases hq
          have hq'p : q' ≠ p := by rintro rfl; rw [hloc, Function.update_self] at hq'; cases hq'
          exact hI.uniq q q' (by rwa [hlocq q hqp] at hq) (by rwa [hlocq q' hq'p] at hq')
        · by_cases hq : q = p
          · subst hq; unfold St; rw [hloc, Function.update_self, hpend, Function.update_self]
          · simpa using (hI.st q).transfer (M := []) (hlocq q hq)
              (by rw [hpend, Function.update_of_ne hq]) (curOp_append_ret_of_ne _ _ (Ne.symm hq))
              (fun _ h => opOf_append_of_eq_some h _) (by simp) (by rw [hmem]; exact id)
              (by rw [hmem])

/-- **Theorem 5** (Attiya–Castañeda–Enea, PODC 2024): the implementation of Section 4.1 is a
wait-free strongly-linearizable implementation of readable test&set from test&set and a
read/write register. -/
theorem theorem5 : (impl P).WaitFree ∧ (impl P).StronglyLinearizable := by
  refine ⟨?_, (impl P).stronglyLinearizable_of_linSim _ linSim⟩
  refine (impl P).waitFree_of_potential (fun _ l => match l with
    | .tasAcc => 2 | .tasWr _ => 1 | .readAcc => 1 | _ => 0) ?_
  intro p l i o k hact x
  cases l with
  | idle => simp [impl] at hact
  | retv b => simp [impl] at hact
  | tasAcc =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]; simp
  | tasWr b =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]; simp
  | readAcc =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]; simp

end StrongLinCN2.RTAS
