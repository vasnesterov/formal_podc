import Podc.SharedMemory.Objects.MaxRegister
import Podc.SharedMemory.Objects.TestAndSet
import Podc.SharedMemory.Potential
import Podc.SharedMemory.StrongLin.Basic

/-!
# Readable multi-shot test&set from a max register and readable test&set (Theorem 6)

Attiya, Castañeda and Enea, *Strong Linearizability using Primitives with Consensus Number 2*,
PODC 2024, Section 4.1. The processes share a max register `curr` (base object `maxRegObj`,
**initialized to `1`**) and an infinite array `TS[1], TS[2], …` of readable test&set objects
(`rtasObj`, all initially `0` = `false`; `TS[0]` exists in the model but is never accessed).

* `test&set()`: `c ← curr.readMax()`; return `TS[c].test&set()`.
* `read()`: `c ← curr.readMax()`; return `TS[c].read()`.
* `reset()`: `c ← curr.readMax()`; `b ← TS[c].read()`; if `b = 1` then `curr.writeMax(c + 1)`;
  return (the acknowledgement `false`, as in `mtasObj`).

Linearization (paper): `curr` only grows by one, and the abstract state is `TS[curr]`. Let
`e_v` be the `writeMax(v + 1)` that changes `curr` from `v` to `v + 1`. Before `e_v`, the
operations that read `v` from `curr` are linearized at their access to `TS[v]` (a reset that
reads `0` there is a no-op reset on state `0`). At `e_v` we linearize, in this order: all
test&set/read operations that read `v` from `curr` and have not accessed `TS[v]` yet (they all
obtain `1`), the resetting operation, and all other resets that read `v` from `curr` and are not
yet linearized (they have not read `TS[v]`, or read `1` and have not executed `writeMax(v + 1)`).
A reset whose `writeMax` does not change `curr` was linearized at an earlier `e_u`. We prove
that this is a forward simulation (`linSim`), hence strong linearizability; wait-freedom is
immediate (at most three accesses per operation).

Processes: any finite type `P` (finiteness is used to list the operations linearized at `e_v`).
-/

namespace StrongLinCN2.MTAS

open Cslib.SharedMemory

/-- Base objects: the max register `curr` and the readable test&set objects `TS[v]`. -/
inductive Obj where
  | curr
  | ts (v : ℕ)
  deriving DecidableEq

/-- Specifications of the base objects. -/
abbrev B : Obj → ObjSpec
  | .curr => maxRegObj
  | .ts _ => rtasObj

/-- The primitive applied to `TS[c]` by an operation (`reset` reads it). -/
def tsOp : MTASOp → RTASOp
  | .tas => .tas
  | .read => .read
  | .reset => .read

/-- Local states (program counters). -/
inductive Loc where
  | idle
  /-- Operation `o`, about to read `curr`. -/
  | start (o : MTASOp)
  /-- Operation `o`, read `c` from `curr`, about to access `TS[c]`. -/
  | acc (o : MTASOp) (c : ℕ)
  /-- `reset`, read `c` from `curr` and `1` from `TS[c]`, about to `writeMax(c + 1)`. -/
  | wr (c : ℕ)
  /-- About to return `b`. -/
  | retv (b : Bool)
  deriving DecidableEq

/-- The local state after the access to `TS[c]` returned `b`. -/
def afterTS : MTASOp → ℕ → Bool → Loc
  | .reset, c, b => if b then .wr c else .retv false
  | _, _, b => .retv b

variable (P : Type) [DecidableEq P]

/-- The implementation of Section 4.1 (multi-shot test&set). -/
def impl : Impl mtasObj B P Loc where
  memInit
    | .curr => (1 : ℕ)
    | .ts _ => false
  locInit _ := .idle
  invoke _ _ o := .start o
  act _
    | .idle => .ret false .idle
    | .start o => .access Obj.curr MaxOp.readMax (fun c => .acc o c)
    | .acc o c => .access (Obj.ts c) (tsOp o) (fun b => afterTS o c b)
    | .wr c => .access Obj.curr (MaxOp.writeMax (c + 1)) (fun _ => .retv false)
    | .retv b => .ret b .idle

set_option linter.unusedSectionVars false

variable {P}

/-! ## Auxiliary facts about the objects -/

/-- The bit of `TS[c]` after applying `tsOp o` to it in state `b`. -/
def tsSet : MTASOp → Bool → Bool
  | .tas, _ => true
  | _, b => b

lemma δ_tsOp (b : Bool) (o : MTASOp) : rtasObj.δ b (tsOp o) = (tsSet o b, b) := by
  cases o <;> rfl

/-! ## The simulation invariant -/

/-- Status of a process. `V = curr`; operations that read an older value `c < V` from `curr`
are already linearized (at `e_c`), with the response they get in state `1` (`true`). -/
def St (α : List (Label P mtasObj)) (C : Config mtasObj B P Loc)
    (Lin : List (OpId P × mtasObj.Op)) (p : P) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .start o => C.pend p = some o ∧ curOp α p ∉ Lin.map Prod.fst ∧ opOf α (curOp α p) = some o
  | .acc o c => C.pend p = some o ∧ opOf α (curOp α p) = some o ∧ 1 ≤ c ∧ c ≤ C.mem .curr ∧
      (c = C.mem .curr → curOp α p ∉ Lin.map Prod.fst) ∧
      (c < C.mem .curr → mtasObj.respIn mtasObj.init Lin (curOp α p) = some (mtasObj.δ true o).2)
  | .wr c => C.pend p = some .reset ∧ opOf α (curOp α p) = some .reset ∧ 1 ≤ c ∧
      c ≤ C.mem .curr ∧ C.mem (.ts c) = true ∧
      (c = C.mem .curr → curOp α p ∉ Lin.map Prod.fst) ∧
      (c < C.mem .curr → mtasObj.respIn mtasObj.init Lin (curOp α p) = some false)
  | .retv b => C.pend p ≠ none ∧ mtasObj.respIn mtasObj.init Lin (curOp α p) = some b

/-- The simulation invariant: the abstract state is `TS[curr]`; the entries below `curr` are set,
those above are unset. -/
structure Inv (α : List (Label P mtasObj)) (C : Config mtasObj B P Loc)
    (Lin : List (OpId P × mtasObj.Op)) : Prop where
  lin : IsLinearization α Lin
  one : 1 ≤ C.mem .curr
  abs : linState Lin = C.mem (.ts (C.mem .curr))
  below : ∀ c : ℕ, 1 ≤ c → c < C.mem .curr → C.mem (.ts c) = true
  above : ∀ c : ℕ, C.mem .curr < c → C.mem (.ts c) = false
  st : ∀ p, St α C Lin p

lemma not_mem_append {Lin M : List (OpId P × mtasObj.Op)} {x : OpId P}
    (h1 : x ∉ Lin.map Prod.fst) (h2 : x ∉ M.map Prod.fst) : x ∉ (Lin ++ M).map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or]; exact ⟨h1, h2⟩

/-- Transfer of the status of a process whose local state and pending operation do not change,
when the linearization is extended without it, `curr` does not change and no `TS` entry is
unset. -/
lemma St.transfer {α α' : List (Label P mtasObj)} {C C' : Config mtasObj B P Loc}
    {Lin M : List (OpId P × mtasObj.Op)} {q : P} (h : St α C Lin q)
    (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q) (hcur : curOp α' q = curOp α q)
    (hop : ∀ o, opOf α (curOp α q) = some o → opOf α' (curOp α q) = some o)
    (hM : curOp α q ∉ M.map Prod.fst) (hV : C'.mem .curr = C.mem .curr)
    (hts : ∀ c, C.mem (.ts c) = true → C'.mem (.ts c) = true) :
    St α' C' (Lin ++ M) q := by
  unfold St at h ⊢
  rw [hloc, hpend, hcur, hV]
  split at h
  · exact h
  · exact ⟨h.1, not_mem_append h.2.1 hM, hop _ h.2.2⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, hop _ h2, h3, h4, fun e => not_mem_append (h5 e) hM,
      fun e => ObjSpec.respIn_append_of_eq_some (h6 e) _⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨h1, hop _ h2, h3, h4, hts _ h5, fun e => not_mem_append (h6 e) hM,
      fun e => ObjSpec.respIn_append_of_eq_some (h7 e) _⟩
  · exact ⟨h.1, ObjSpec.respIn_append_of_eq_some h.2 _⟩

/-! ## The operations linearized at `e_v` -/

/-- Test&set/read operations that read `V` from `curr` and have not accessed `TS[V]`. -/
def g1 (V : ℕ) : Loc → Bool
  | .acc .tas c => decide (c = V)
  | .acc .read c => decide (c = V)
  | _ => false

/-- Resets that read `V` from `curr` and are not linearized yet. -/
def g3 (V : ℕ) : Loc → Bool
  | .acc .reset c => decide (c = V)
  | .wr c => decide (c = V)
  | _ => false

/-- The operation of a local state (dummy for `idle`/`retv`). -/
def lop : Loc → MTASOp
  | .start o => o
  | .acc o _ => o
  | _ => .reset

lemma g1_iff (V : ℕ) (l : Loc) : g1 V l = true ↔ ∃ o, o ≠ .reset ∧ l = .acc o V := by
  cases l with
  | acc o c => cases o <;> simp [g1, eq_comm]
  | _ => simp [g1]

lemma g3_iff (V : ℕ) (l : Loc) : g3 V l = true ↔ l = .acc .reset V ∨ l = .wr V := by
  cases l with
  | acc o c => cases o <;> simp [g3, eq_comm]
  | wr c => simp [g3, eq_comm]
  | _ => simp [g3]

lemma linSim [Fintype P] : (impl P).LinSim Inv where
  init := by
    refine ⟨isLinearization_nil, le_rfl, rfl, ?_, fun c _ => rfl, fun p => ?_⟩
    · intro c h1 h2
      exact absurd h2 (by change ¬ c < 1; omega)
    · simp [St, impl, Impl.initCfg]
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
      have hnot : curOp α p ∉ Lin.map Prod.fst := by
        intro hm
        have := hI.lin.invoked_of_mem hm
        simp [Invoked] at this; omega
      have hop : opOf (α ++ [.inv p o]) (curOp α p) = some o := by
        simp [opOf, opsOf_append, ← hlen]
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      refine ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.one, by rw [hmem]; exact hI.abs,
        by rw [hmem]; exact hI.below, by rw [hmem]; exact hI.above, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        unfold St
        rw [hloc, Function.update_self, hpend, Function.update_self, curOp_append_inv]
        exact ⟨rfl, hnot, hop⟩
      · simpa using (hI.st q).transfer (α' := α ++ [.inv p o]) (C' := C') (M := [])
          (by rw [hloc, Function.update_of_ne hq]) (by rw [hpend, Function.update_of_ne hq])
          (curOp_append_inv _ _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp)
          (by rw [hmem]) (fun c h => by rw [hmem]; exact h)
    | tau p =>
      obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hstep
      have hlocq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hpendq : ∀ q, C'.pend q = C.pend q := fun q => by rw [hpend]
      have hst := hI.st p
      cases hl : C.loc p with
      | idle => simp [impl, hl] at hact
      | retv b => simp [impl, hl] at hact
      | start o' =>
        -- `readMax` on `curr`: no linearization
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have ho' : o = MaxOp.readMax := (eq_of_heq ho).symm
        subst ho'
        have hk' : k = fun c => Loc.acc o' c := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp2, hp3⟩ := hst
        have hmem' : C'.mem = C.mem := by
          rw [hmem]; exact Function.update_eq_self _ _
        have hlocp : C'.loc p = .acc o' (C.mem .curr) := by
          rw [hloc, Function.update_self]
        refine ⟨[], ?_⟩
        rw [List.append_nil]
        refine ⟨hI.lin.append_tau p, by rw [hmem']; exact hI.one, by rw [hmem']; exact hI.abs,
          by rw [hmem']; exact hI.below, by rw [hmem']; exact hI.above, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq
          unfold St
          rw [hlocp, hpend, curOp_append_tau, hmem']
          exact ⟨hp1, opOf_append_of_eq_some hp3 _, hI.one, le_rfl, fun _ => hp2,
            fun h => absurd h (lt_irrefl _)⟩
        · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
            (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp)
            (by rw [hmem']) (fun c h => by rw [hmem']; exact h)
      | acc o' c =>
        -- access to `TS[c]`
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have ho' : o = tsOp o' := (eq_of_heq ho).symm
        subst ho'
        have hk' : k = fun b => afterTS o' c b := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp3, hc1, hcV, hpeq, hplt⟩ := hst
        have hnc : ¬ Completed α (curOp α p) := by simp [Completed]
        have hδ : (B (.ts c)).δ (C.mem (.ts c)) (tsOp o') =
            (tsSet o' (C.mem (.ts c)), C.mem (.ts c)) := δ_tsOp _ _
        rw [hδ] at hmem hloc
        have hlocp : C'.loc p = afterTS o' c (C.mem (.ts c)) := by
          rw [hloc, Function.update_self]
        have hV : C'.mem .curr = C.mem .curr := by
          rw [hmem]; exact Function.update_of_ne (by simp) _ _
        have hts : ∀ c', C.mem (.ts c') = true → C'.mem (.ts c') = true := by
          intro c' h
          rw [hmem]
          by_cases hc : c' = c
          · subst hc; rw [Function.update_self, h]; cases o' <;> rfl
          · rw [Function.update_of_ne (by simpa using hc)]; exact h
        have hmts : ∀ c', c' ≠ c → C'.mem (.ts c') = C.mem (.ts c') := by
          intro c' hc; rw [hmem, Function.update_of_ne (by simpa using hc)]
        rcases Nat.lt_or_eq_of_le hcV with hlt | heq
        · -- an older value: already linearized, `TS[c]` is set
          have hTS : C.mem (.ts c) = true := hI.below c hc1 hlt
          have hmem' : C'.mem = C.mem := by
            rw [hmem, Function.update_eq_self_iff, hTS]; cases o' <;> rfl
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          refine ⟨hI.lin.append_tau p, by rw [hmem']; exact hI.one, by rw [hmem']; exact hI.abs,
            by rw [hmem']; exact hI.below, by rw [hmem']; exact hI.above, fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            unfold St
            rw [hlocp, hpend, curOp_append_tau, hmem', hTS]
            have hr := hplt hlt
            cases o' with
            | tas => exact ⟨by rw [hp1]; simp, hr⟩
            | read => exact ⟨by rw [hp1]; simp, hr⟩
            | reset =>
              exact ⟨hp1, opOf_append_of_eq_some hp3 _, hc1, hcV, hTS,
                fun h => absurd h (Nat.ne_of_lt hlt), fun _ => hr⟩
          · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
              (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp)
              (by rw [hmem']) (fun c h => by rw [hmem']; exact h)
        · -- the current value
          subst heq
          have hp2 := hpeq rfl
          set V := C.mem .curr with hVdef
          have hb : linState Lin = C.mem (.ts V) := hI.abs
          have hothers : ∀ (M : List (OpId P × mtasObj.Op)), (∀ y ∈ M.map Prod.fst, y.1 = p) →
              ∀ q, q ≠ p → St (α ++ [.tau p]) C' (Lin ++ M) q := by
            intro M hM q hq
            exact (hI.st q).transfer (hlocq q hq) (hpendq q) (curOp_append_tau _ _ _)
              (fun _ h => opOf_append_of_eq_some h _) (fun h => hq (hM _ h)) hV hts
          cases o' with
          | tas =>
            have hTS' : C'.mem (.ts V) = true := by rw [hmem, Function.update_self]; rfl
            refine ⟨[(curOp α p, .tas)], (hI.lin.push hp3 hp2 hnc).append_tau p,
              (by rw [hV]; exact hI.one), ?_, ?_, ?_, fun q => ?_⟩
            · rw [linState_concat, hV, hTS']
            · intro c' h1 h2; rw [hV] at h2; rw [hmts c' (Nat.ne_of_lt h2)]; exact hI.below c' h1 h2
            · intro c' h; rw [hV] at h; rw [hmts c' (Nat.ne_of_gt h)]; exact hI.above c' h
            · by_cases hq : q = p
              · subst hq
                unfold St
                rw [hlocp, hpend, curOp_append_tau, ObjSpec.respIn_concat_self hp2]
                exact ⟨by rw [hp1]; simp, congrArg some hb⟩
              · exact hothers _ (by simp) q hq
          | read =>
            have hmem' : C'.mem = C.mem := by
              rw [hmem]; exact Function.update_eq_self _ _
            refine ⟨[(curOp α p, .read)], (hI.lin.push hp3 hp2 hnc).append_tau p,
              (by rw [hmem']; exact hI.one), ?_, (by rw [hmem']; exact hI.below),
              (by rw [hmem']; exact hI.above), fun q => ?_⟩
            · rw [linState_concat, hmem']; exact hI.abs
            · by_cases hq : q = p
              · subst hq
                unfold St
                rw [hlocp, hpend, curOp_append_tau, ObjSpec.respIn_concat_self hp2]
                exact ⟨by rw [hp1]; simp, congrArg some hb⟩
              · exact hothers _ (by simp) q hq
          | reset =>
            have hmem' : C'.mem = C.mem := by
              rw [hmem]; exact Function.update_eq_self _ _
            cases hTS : C.mem (.ts V) with
            | true =>
              -- read `1`: will try to advance `curr`
              refine ⟨[], ?_⟩
              rw [List.append_nil]
              refine ⟨hI.lin.append_tau p, by rw [hmem']; exact hI.one,
                by rw [hmem']; exact hI.abs, by rw [hmem']; exact hI.below,
                by rw [hmem']; exact hI.above, fun q => ?_⟩
              by_cases hq : q = p
              · subst hq
                unfold St
                rw [hlocp, hpend, curOp_append_tau, hmem', hTS]
                exact ⟨hp1, opOf_append_of_eq_some hp3 _, hc1, le_rfl, hTS, fun _ => hp2,
                  fun h => absurd h (lt_irrefl _)⟩
              · simpa using hothers [] (by simp) q hq
            | false =>
              -- read `0`: a no-op reset on state `0`
              refine ⟨[(curOp α p, .reset)], (hI.lin.push hp3 hp2 hnc).append_tau p,
                by rw [hmem']; exact hI.one, ?_, by rw [hmem']; exact hI.below,
                by rw [hmem']; exact hI.above, fun q => ?_⟩
              · rw [linState_concat, hmem', hTS]
              · by_cases hq : q = p
                · subst hq
                  unfold St
                  rw [hlocp, hpend, curOp_append_tau, ObjSpec.respIn_concat_self hp2, hTS]
                  exact ⟨by rw [hp1]; simp, rfl⟩
                · exact hothers _ (by simp) q hq
      | wr c =>
        -- `writeMax(c + 1)` on `curr`
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        have ho' : o = MaxOp.writeMax (c + 1) := (eq_of_heq ho).symm
        subst ho'
        have hk' : k = fun _ => Loc.retv false := (eq_of_heq hk).symm
        subst hk'
        unfold St at hst; rw [hl] at hst
        obtain ⟨hp1, hp3, hc1, hcV, hpts, hpeq, hplt⟩ := hst
        have hlocp : C'.loc p = .retv false := by rw [hloc, Function.update_self]
        have hmts : ∀ c', C'.mem (.ts c') = C.mem (.ts c') := fun c' => by
          rw [hmem]; exact Function.update_of_ne (by simp) _ _
        have hVnew : C'.mem .curr = max (C.mem .curr) (c + 1) := by
          rw [hmem, Function.update_self]
        rcases Nat.lt_or_eq_of_le hcV with hlt | heq
        · -- `curr` does not change: already linearized
          have hV : C'.mem .curr = C.mem .curr := by rw [hVnew]; exact Nat.max_eq_left (by omega)
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          refine ⟨hI.lin.append_tau p, by rw [hV]; exact hI.one, by rw [hV, hmts]; exact hI.abs,
            fun c' h1 h2 => by rw [hmts]; exact hI.below c' h1 (by rwa [hV] at h2),
            fun c' h => by rw [hmts]; exact hI.above c' (by rwa [hV] at h), fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            unfold St
            rw [hlocp, hpend, curOp_append_tau]
            exact ⟨by rw [hp1]; simp, hplt hlt⟩
          · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
              (curOp_append_tau _ _ _) (fun _ h => opOf_append_of_eq_some h _) (by simp) hV
              (fun c h => by rw [hmts]; exact h)
        · -- the event `e_V`
          subst heq
          have hp2 := hpeq rfl
          set V : ℕ := C.mem .curr with hVdef
          have hV : C'.mem .curr = V + 1 := by rw [hVnew]; exact Nat.max_eq_right (by omega)
          let l1 : List P := (Finset.univ.filter (fun q => g1 V (C.loc q) = true)).toList
          let l3 : List P :=
            (Finset.univ.filter (fun q => q ≠ p ∧ g3 V (C.loc q) = true)).toList
          let M1 : List (OpId P × mtasObj.Op) := l1.map (fun q => (curOp α q, lop (C.loc q)))
          let M3 : List (OpId P × mtasObj.Op) := l3.map (fun q => (curOp α q, MTASOp.reset))
          let M : List (OpId P × mtasObj.Op) := M1 ++ (curOp α p, .reset) :: M3
          have hl1 : ∀ q, q ∈ l1 ↔ ∃ o, o ≠ .reset ∧ C.loc q = .acc o V := by
            intro q; simp [l1, g1_iff]
          have hl3 : ∀ q, q ∈ l3 ↔ q ≠ p ∧ (C.loc q = .acc .reset V ∨ C.loc q = .wr V) := by
            intro q; simp [l3, g3_iff]
          have hcurinj : Function.Injective (curOp α) := fun a b h => congrArg Prod.fst h
          have hM1fst : M1.map Prod.fst = l1.map (curOp α) := by simp [M1, Function.comp_def]
          have hM3fst : M3.map Prod.fst = l3.map (curOp α) := by simp [M3, Function.comp_def]
          have hMfst : M.map Prod.fst = (l1 ++ p :: l3).map (curOp α) := by
            simp only [M, List.map_append, List.map_cons, hM1fst, hM3fst]
          have hmemM1 : ∀ q, curOp α q ∈ M1.map Prod.fst ↔ q ∈ l1 := by
            intro q; rw [hM1fst]; exact List.mem_map_of_injective hcurinj
          have hmemM3 : ∀ q, curOp α q ∈ M3.map Prod.fst ↔ q ∈ l3 := by
            intro q; rw [hM3fst]; exact List.mem_map_of_injective hcurinj
          have hmemM : ∀ q, curOp α q ∈ M.map Prod.fst ↔ q ∈ l1 ∨ q = p ∨ q ∈ l3 := by
            intro q
            rw [hMfst, List.mem_map_of_injective hcurinj]
            simp
          have hpl1 : p ∉ l1 := by rw [hl1]; rintro ⟨o, -, h⟩; rw [hl] at h; cases h
          have hpl3 : p ∉ l3 := by rw [hl3]; rintro ⟨h, -⟩; exact h rfl
          have hl13 : ∀ q, q ∈ l1 → q ∉ l3 := by
            intro q h1 h3
            obtain ⟨o, -, h⟩ := (hl1 q).1 h1
            rcases ((hl3 q).1 h3).2 with h' | h' <;> rw [h] at h' <;> cases h'
            simp_all
          -- statuses of the processes in `M`
          have hstl1 : ∀ q ∈ l1, ∃ o, o ≠ .reset ∧ C.loc q = .acc o V ∧
              opOf α (curOp α q) = some o ∧ curOp α q ∉ Lin.map Prod.fst := by
            intro q hq
            obtain ⟨o, ho, h⟩ := (hl1 q).1 hq
            have := hI.st q
            unfold St at this; rw [h] at this
            exact ⟨o, ho, h, this.2.1, this.2.2.2.2.1 rfl⟩
          have hstl3 : ∀ q ∈ l3, opOf α (curOp α q) = some .reset ∧
              curOp α q ∉ Lin.map Prod.fst := by
            intro q hq
            rcases ((hl3 q).1 hq).2 with h | h
            · have := hI.st q
              unfold St at this; rw [h] at this
              exact ⟨this.2.1, this.2.2.2.2.1 rfl⟩
            · have := hI.st q
              unfold St at this; rw [h] at this
              exact ⟨this.2.1, this.2.2.2.2.2.1 rfl⟩
          have hMnd : (M.map Prod.fst).Nodup := by
            rw [hMfst]
            refine List.Nodup.map hcurinj ?_
            rw [List.nodup_append]
            refine ⟨Finset.nodup_toList _, List.nodup_cons.2 ⟨hpl3, Finset.nodup_toList _⟩, ?_⟩
            intro a ha b hb hab
            subst hab
            rcases List.mem_cons.1 hb with rfl | hb
            · exact hpl1 ha
            · exact hl13 a ha hb
          have hlinM : IsLinearization α (Lin ++ M) := by
            refine hI.lin.push_list M ?_ hMnd ?_
            · intro y hy
              simp only [M, M1, M3, List.mem_append, List.mem_cons, List.mem_map] at hy
              rcases hy with ⟨q, hq, rfl⟩ | rfl | ⟨q, hq, rfl⟩
              · obtain ⟨o, -, h, h1, -⟩ := hstl1 q hq
                exact ⟨by rw [h]; exact h1, by simp [Completed]⟩
              · exact ⟨hp3, by simp [Completed]⟩
              · exact ⟨(hstl3 q hq).1, by simp [Completed]⟩
            · intro y hy
              simp only [M, M1, M3, List.mem_append, List.mem_cons, List.mem_map] at hy
              rcases hy with ⟨q, hq, rfl⟩ | rfl | ⟨q, hq, rfl⟩
              · obtain ⟨-, -, -, -, h⟩ := hstl1 q hq; exact h
              · exact hp2
              · exact (hstl3 q hq).2
          -- the abstract state and the responses assigned by `Lin ++ M`
          have hLin : linState Lin = true := by rw [hI.abs]; exact hpts
          have hLin' : mtasObj.runOps mtasObj.init (Lin.map Prod.snd) = true := hLin
          have hM1c : ∀ y ∈ M1, mtasObj.δ true y.2 = (true, true) := by
            intro y hy
            simp only [M1, List.mem_map] at hy
            obtain ⟨q, hq, rfl⟩ := hy
            obtain ⟨o, ho, h, -⟩ := hstl1 q hq
            simp only [h, lop]
            cases o <;> simp_all
          have hM3c : ∀ y ∈ M3, mtasObj.δ false y.2 = (false, false) := by
            intro y hy
            simp only [M3, List.mem_map] at hy
            obtain ⟨q, -, rfl⟩ := hy
            rfl
          have hLM : linState (Lin ++ M) = false := by
            rw [linState_append, hLin]
            simp only [M, List.map_append, List.map_cons]
            rw [ObjSpec.runOps_append, ObjSpec.runOps_map_snd_const true hM1c, ObjSpec.runOps_cons]
            exact ObjSpec.runOps_map_snd_const false hM3c
          have hrespM1 : ∀ q ∈ l1, mtasObj.respIn mtasObj.init (Lin ++ M) (curOp α q) = some true := by
            intro q hq
            obtain ⟨-, -, -, -, hnl⟩ := hstl1 q hq
            rw [ObjSpec.respIn_append_of_not_mem hnl, hLin']
            exact ObjSpec.respIn_append_const _ hM1c ((hmemM1 q).2 hq) _
          have hrespP : mtasObj.respIn mtasObj.init (Lin ++ M) (curOp α p) = some false := by
            rw [ObjSpec.respIn_append_of_not_mem hp2, hLin',
              ObjSpec.respIn_append_of_not_mem (fun h => hpl1 ((hmemM1 p).1 h)),
              ObjSpec.runOps_map_snd_const true hM1c, ObjSpec.respIn_cons_self]
          have hrespM3 : ∀ q ∈ l3, mtasObj.respIn mtasObj.init (Lin ++ M) (curOp α q) = some false := by
            intro q hq
            have hqp : q ≠ p := ((hl3 q).1 hq).1
            rw [ObjSpec.respIn_append_of_not_mem (hstl3 q hq).2, hLin',
              ObjSpec.respIn_append_of_not_mem (fun h => hl13 q ((hmemM1 q).1 h) hq),
              ObjSpec.runOps_map_snd_const true hM1c,
              ObjSpec.respIn_cons_of_ne _ _ _ (fun h => hqp (congrArg Prod.fst h).symm)]
            have := ObjSpec.respIn_append_const (q := false) false hM3c ((hmemM3 q).2 hq) []
            rwa [List.append_nil] at this
          refine ⟨M, hlinM.append_tau p, by rw [hV]; exact Nat.le_add_left 1 V, ?_, ?_, ?_, fun q => ?_⟩
          · rw [hLM, hV, hmts]; exact (hI.above (V + 1) (Nat.lt_succ_self _)).symm
          · intro c' h1 h2
            rw [hV] at h2; rw [hmts]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with h | rfl
            · exact hI.below c' h1 h
            · exact hpts
          · intro c' h; rw [hV] at h; rw [hmts]; exact hI.above c' (Nat.lt_of_succ_lt h)
          · by_cases hq : q = p
            · subst hq
              unfold St
              rw [hlocp, hpend, curOp_append_tau]
              exact ⟨by rw [hp1]; simp, hrespP⟩
            · have hqst := hI.st q
              unfold St at hqst ⊢
              rw [hlocq q hq, hpendq q, curOp_append_tau, hV]
              cases hc : C.loc q with
              | idle => rw [hc] at hqst; exact hqst
              | start o =>
                rw [hc] at hqst
                refine ⟨hqst.1, not_mem_append hqst.2.1 ?_, opOf_append_of_eq_some hqst.2.2 _⟩
                rw [hmemM]
                rintro (h | h | h)
                · obtain ⟨o', -, h'⟩ := (hl1 q).1 h; rw [hc] at h'; cases h'
                · exact hq h
                · rcases ((hl3 q).1 h).2 with h' | h' <;> rw [hc] at h' <;> cases h'
              | acc o c' =>
                rw [hc] at hqst
                obtain ⟨h1, h2, h3, h4, -, h6⟩ := hqst
                refine ⟨h1, opOf_append_of_eq_some h2 _, h3, by omega, fun h => by omega,
                  fun _ => ?_⟩
                rcases Nat.lt_or_eq_of_le h4 with h | rfl
                · exact ObjSpec.respIn_append_of_eq_some (h6 h) _
                · cases o with
                  | tas => exact hrespM1 q ((hl1 q).2 ⟨_, by simp, hc⟩)
                  | read => exact hrespM1 q ((hl1 q).2 ⟨_, by simp, hc⟩)
                  | reset => exact hrespM3 q ((hl3 q).2 ⟨hq, Or.inl hc⟩)
              | wr c' =>
                rw [hc] at hqst
                obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hqst
                refine ⟨h1, opOf_append_of_eq_some h2 _, h3, by omega, by rw [hmts]; exact h5,
                  fun h => by omega, fun _ => ?_⟩
                rcases Nat.lt_or_eq_of_le h4 with h | rfl
                · exact ObjSpec.respIn_append_of_eq_some (h7 h) _
                · exact hrespM3 q ((hl3 q).2 ⟨hq, Or.inr hc⟩)
              | retv b =>
                rw [hc] at hqst
                exact ⟨hqst.1, ObjSpec.respIn_append_of_eq_some hqst.2 _⟩
    | ret p r =>
      obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
      have hst := hI.st p
      cases hl : C.loc p with
      | idle => unfold St at hst; rw [hl] at hst; exact absurd hst h0
      | start o => simp [impl, hl] at hact
      | acc o c => simp [impl, hl] at hact
      | wr c => simp [impl, hl] at hact
      | retv b =>
        simp only [impl, hl, Action.ret.injEq] at hact
        obtain ⟨rfl, rfl⟩ := hact
        unfold St at hst; rw [hl] at hst
        refine ⟨[], ?_⟩
        rw [List.append_nil]
        refine ⟨hI.lin.append_ret_of_respIn hst.2, by rw [hmem]; exact hI.one,
          by rw [hmem]; exact hI.abs, by rw [hmem]; exact hI.below, by rw [hmem]; exact hI.above,
          fun q => ?_⟩
        by_cases hq : q = p
        · subst hq; unfold St; rw [hloc, Function.update_self, hpend, Function.update_self]
        · simpa using (hI.st q).transfer (M := []) (by rw [hloc, Function.update_of_ne hq])
            (by rw [hpend, Function.update_of_ne hq]) (curOp_append_ret_of_ne _ _ (Ne.symm hq))
            (fun _ h => opOf_append_of_eq_some h _) (by simp) (by rw [hmem])
            (fun c h => by rw [hmem]; exact h)

/-- **Theorem 6** (Attiya–Castañeda–Enea, PODC 2024): the implementation of Section 4.1 is a
wait-free strongly-linearizable implementation of readable multi-shot test&set from a max
register and readable test&set objects. -/
theorem theorem6 [Fintype P] : (impl P).WaitFree ∧ (impl P).StronglyLinearizable := by
  refine ⟨?_, (impl P).stronglyLinearizable_of_linSim _ linSim⟩
  refine (impl P).waitFree_of_potential (fun _ l => match l with
    | .start _ => 3 | .acc _ _ => 2 | .wr _ => 1 | _ => 0) ?_
  intro p l i o k hact x
  cases l with
  | idle => simp [impl] at hact
  | retv b => simp [impl] at hact
  | start o' =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]; simp
  | acc o' c =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]
    cases o' <;> cases x <;> simp [afterTS]
  | wr c =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]; simp

end StrongLinCN2.MTAS
