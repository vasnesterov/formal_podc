import Podc.StrongLin.Basic
import Podc.SharedMemory.Objects
import Podc.SharedMemory.Potential

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

lemma linState_append_single (Lin : List (OpId P × mtasObj.Op)) (x : OpId P) (o : MTASOp) :
    linState (Lin ++ [(x, o)]) = (mtasObj.δ (linState Lin) o).1 := by
  rw [linState, List.map_append, ObjSpec.runOps_append]; rfl

-- CSLib candidate (with `runOps_const`)
/-- Operations that keep the state `q` and return `r` can be linearized in any number. -/
lemma linRespFrom_const {A : ObjSpec} (x : OpId P) (q : A.State) (r : A.Resp)
    (l L' : List (OpId P × A.Op)) (hl : ∀ y ∈ l, A.δ q y.2 = (q, r))
    (hx : x ∈ l.map Prod.fst) : linRespFrom A x q (l ++ L') = some r := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    obtain ⟨y, o⟩ := y
    have hy := hl (y, o) (by simp)
    simp only [List.cons_append, linRespFrom, hy]
    split_ifs with h
    · rfl
    · simp only [List.map_cons, List.mem_cons] at hx
      exact ih (fun z hz => hl z (by simp [hz])) (hx.resolve_left (Ne.symm h))

lemma runOps_const {A : ObjSpec} (q : A.State) (r : A.Resp) (l : List (OpId P × A.Op))
    (hl : ∀ y ∈ l, A.δ q y.2 = (q, r)) : A.runOps q (l.map Prod.snd) = q := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, ObjSpec.runOps_cons, hl y (by simp)]
    exact ih (fun z hz => hl z (by simp [hz]))

/-! ## The simulation invariant -/

/-- The current instance of `p`. -/
abbrev cur (α : List (Label P mtasObj)) (p : P) : OpId P := (p, (respsOf α p).length)

/-- Status of a process. `V = curr`; operations that read an older value `c < V` from `curr`
are already linearized (at `e_c`), with the response they get in state `1` (`true`). -/
def St (α : List (Label P mtasObj)) (C : Config mtasObj B P Loc)
    (Lin : List (OpId P × mtasObj.Op)) (p : P) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .start o => C.pend p = some o ∧ cur α p ∉ Lin.map Prod.fst ∧ opOf α (cur α p) = some o
  | .acc o c => C.pend p = some o ∧ opOf α (cur α p) = some o ∧ 1 ≤ c ∧ c ≤ C.mem .curr ∧
      (c = C.mem .curr → cur α p ∉ Lin.map Prod.fst) ∧
      (c < C.mem .curr → linResp Lin (cur α p) = some (mtasObj.δ true o).2)
  | .wr c => C.pend p = some .reset ∧ opOf α (cur α p) = some .reset ∧ 1 ≤ c ∧
      c ≤ C.mem .curr ∧ C.mem (.ts c) = true ∧
      (c = C.mem .curr → cur α p ∉ Lin.map Prod.fst) ∧
      (c < C.mem .curr → linResp Lin (cur α p) = some false)
  | .retv b => C.pend p ≠ none ∧ linResp Lin (cur α p) = some b

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

lemma cur_append_inv (α : List (Label P mtasObj)) (p q : P) (o : mtasObj.Op) :
    cur (α ++ [.inv p o]) q = cur α q := by simp [cur, respsOf_append]

lemma cur_append_tau (α : List (Label P mtasObj)) (p q : P) :
    cur (α ++ [.tau p]) q = cur α q := by simp [cur, respsOf_append]

lemma cur_append_ret_of_ne (α : List (Label P mtasObj)) {p q : P} (r : Bool) (h : p ≠ q) :
    cur (α ++ [.ret p r]) q = cur α q := by simp [cur, respsOf_append, h]

lemma opOf_append_of_opOf {α : List (Label P mtasObj)} {x : OpId P} {o : mtasObj.Op}
    (ℓ : Label P mtasObj) (h : opOf α x = some o) : opOf (α ++ [ℓ]) x = some o := by
  have hinv : Invoked α x := by simp only [opOf] at h; exact (List.getElem?_eq_some_iff.1 h).1
  rw [opOf_append_of_invoked hinv, h]

lemma linResp_append_of_some {Lin : List (OpId P × mtasObj.Op)} {x : OpId P} {b : Bool}
    (M : List (OpId P × mtasObj.Op)) (h : linResp Lin x = some b) :
    linResp (Lin ++ M) x = some b := by
  rw [linResp_append_of_mem _ (linResp_isSome_iff.1 (by rw [h]; rfl)), h]

lemma not_mem_append {Lin M : List (OpId P × mtasObj.Op)} {x : OpId P}
    (h1 : x ∉ Lin.map Prod.fst) (h2 : x ∉ M.map Prod.fst) : x ∉ (Lin ++ M).map Prod.fst := by
  simp only [List.map_append, List.mem_append, not_or]; exact ⟨h1, h2⟩

/-- Transfer of the status of a process whose local state and pending operation do not change,
when the linearization is extended without it, `curr` does not change and no `TS` entry is
unset. -/
lemma St.transfer {α α' : List (Label P mtasObj)} {C C' : Config mtasObj B P Loc}
    {Lin M : List (OpId P × mtasObj.Op)} {q : P} (h : St α C Lin q)
    (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q) (hcur : cur α' q = cur α q)
    (hop : ∀ o, opOf α (cur α q) = some o → opOf α' (cur α q) = some o)
    (hM : cur α q ∉ M.map Prod.fst) (hV : C'.mem .curr = C.mem .curr)
    (hts : ∀ c, C.mem (.ts c) = true → C'.mem (.ts c) = true) :
    St α' C' (Lin ++ M) q := by
  unfold St at h ⊢
  rw [hloc, hpend, hcur, hV]
  split at h
  · exact h
  · exact ⟨h.1, not_mem_append h.2.1 hM, hop _ h.2.2⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, hop _ h2, h3, h4, fun e => not_mem_append (h5 e) hM,
      fun e => linResp_append_of_some _ (h6 e)⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    exact ⟨h1, hop _ h2, h3, h4, hts _ h5, fun e => not_mem_append (h6 e) hM,
      fun e => linResp_append_of_some _ (h7 e)⟩
  · exact ⟨h.1, linResp_append_of_some _ h.2⟩

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
      have hnot : cur α p ∉ Lin.map Prod.fst := by
        intro hm
        have := hI.lin.invoked_of_mem hm
        simp [Invoked] at this; omega
      have hop : opOf (α ++ [.inv p o]) (cur α p) = some o := by
        simp [opOf, opsOf_append, ← hlen]
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      refine ⟨hI.lin.append_inv p o, by rw [hmem]; exact hI.one, by rw [hmem]; exact hI.abs,
        by rw [hmem]; exact hI.below, by rw [hmem]; exact hI.above, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        unfold St
        rw [hloc, Function.update_self, hpend, Function.update_self, cur_append_inv]
        exact ⟨rfl, hnot, hop⟩
      · simpa using (hI.st q).transfer (α' := α ++ [.inv p o]) (C' := C') (M := [])
          (by rw [hloc, Function.update_of_ne hq]) (by rw [hpend, Function.update_of_ne hq])
          (cur_append_inv _ _ _ _) (fun o' h => opOf_append_of_opOf _ h) (by simp)
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
          rw [hlocp, hpend, cur_append_tau, hmem']
          exact ⟨hp1, opOf_append_of_opOf _ hp3, hI.one, le_rfl, fun _ => hp2,
            fun h => absurd h (lt_irrefl _)⟩
        · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
            (cur_append_tau _ _ _) (fun o' h => opOf_append_of_opOf _ h) (by simp)
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
        have hnc : ¬ Completed α (cur α p) := by simp [Completed]
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
            rw [hlocp, hpend, cur_append_tau, hmem', hTS]
            have hr := hplt hlt
            cases o' with
            | tas => exact ⟨by rw [hp1]; simp, hr⟩
            | read => exact ⟨by rw [hp1]; simp, hr⟩
            | reset =>
              exact ⟨hp1, opOf_append_of_opOf _ hp3, hc1, hcV, hTS,
                fun h => absurd h (Nat.ne_of_lt hlt), fun _ => hr⟩
          · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
              (cur_append_tau _ _ _) (fun o' h => opOf_append_of_opOf _ h) (by simp)
              (by rw [hmem']) (fun c h => by rw [hmem']; exact h)
        · -- the current value
          subst heq
          have hp2 := hpeq rfl
          set V := C.mem .curr with hVdef
          have hb : linState Lin = C.mem (.ts V) := hI.abs
          have hothers : ∀ (M : List (OpId P × mtasObj.Op)), (∀ y ∈ M.map Prod.fst, y.1 = p) →
              ∀ q, q ≠ p → St (α ++ [.tau p]) C' (Lin ++ M) q := by
            intro M hM q hq
            exact (hI.st q).transfer (hlocq q hq) (hpendq q) (cur_append_tau _ _ _)
              (fun o' h => opOf_append_of_opOf _ h) (fun h => hq (hM _ h)) hV hts
          cases o' with
          | tas =>
            have hTS' : C'.mem (.ts V) = true := by rw [hmem, Function.update_self]; rfl
            refine ⟨[(cur α p, .tas)], (hI.lin.push hp3 hp2 hnc).append_tau p,
              (by rw [hV]; exact hI.one), ?_, ?_, ?_, fun q => ?_⟩
            · rw [linState_append_single, hV, hTS']
            · intro c' h1 h2; rw [hV] at h2; rw [hmts c' (Nat.ne_of_lt h2)]; exact hI.below c' h1 h2
            · intro c' h; rw [hV] at h; rw [hmts c' (Nat.ne_of_gt h)]; exact hI.above c' h
            · by_cases hq : q = p
              · subst hq
                unfold St
                rw [hlocp, hpend, cur_append_tau, linResp_append_singleton_self _ hp2]
                exact ⟨by rw [hp1]; simp, by rw [← hb]⟩
              · exact hothers _ (by simp) q hq
          | read =>
            have hmem' : C'.mem = C.mem := by
              rw [hmem]; exact Function.update_eq_self _ _
            refine ⟨[(cur α p, .read)], (hI.lin.push hp3 hp2 hnc).append_tau p,
              (by rw [hmem']; exact hI.one), ?_, (by rw [hmem']; exact hI.below),
              (by rw [hmem']; exact hI.above), fun q => ?_⟩
            · rw [linState_append_single, hmem']; exact hI.abs
            · by_cases hq : q = p
              · subst hq
                unfold St
                rw [hlocp, hpend, cur_append_tau, linResp_append_singleton_self _ hp2]
                exact ⟨by rw [hp1]; simp, by rw [← hb]⟩
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
                rw [hlocp, hpend, cur_append_tau, hmem', hTS]
                exact ⟨hp1, opOf_append_of_opOf _ hp3, hc1, le_rfl, hTS, fun _ => hp2,
                  fun h => absurd h (lt_irrefl _)⟩
              · simpa using hothers [] (by simp) q hq
            | false =>
              -- read `0`: a no-op reset on state `0`
              refine ⟨[(cur α p, .reset)], (hI.lin.push hp3 hp2 hnc).append_tau p,
                by rw [hmem']; exact hI.one, ?_, by rw [hmem']; exact hI.below,
                by rw [hmem']; exact hI.above, fun q => ?_⟩
              · rw [linState_append_single, hmem', hTS]
              · by_cases hq : q = p
                · subst hq
                  unfold St
                  rw [hlocp, hpend, cur_append_tau, linResp_append_singleton_self _ hp2, hTS]
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
            rw [hlocp, hpend, cur_append_tau]
            exact ⟨by rw [hp1]; simp, hplt hlt⟩
          · simpa using (hI.st q).transfer (M := []) (hlocq q hq) (hpendq q)
              (cur_append_tau _ _ _) (fun o' h => opOf_append_of_opOf _ h) (by simp) hV
              (fun c h => by rw [hmts]; exact h)
        · -- the event `e_V`
          subst heq
          have hp2 := hpeq rfl
          set V : ℕ := C.mem .curr with hVdef
          have hV : C'.mem .curr = V + 1 := by rw [hVnew]; exact Nat.max_eq_right (by omega)
          let l1 : List P := (Finset.univ.filter (fun q => g1 V (C.loc q) = true)).toList
          let l3 : List P :=
            (Finset.univ.filter (fun q => q ≠ p ∧ g3 V (C.loc q) = true)).toList
          let M1 : List (OpId P × mtasObj.Op) := l1.map (fun q => (cur α q, lop (C.loc q)))
          let M3 : List (OpId P × mtasObj.Op) := l3.map (fun q => (cur α q, MTASOp.reset))
          let M : List (OpId P × mtasObj.Op) := M1 ++ (cur α p, .reset) :: M3
          have hl1 : ∀ q, q ∈ l1 ↔ ∃ o, o ≠ .reset ∧ C.loc q = .acc o V := by
            intro q; simp [l1, g1_iff]
          have hl3 : ∀ q, q ∈ l3 ↔ q ≠ p ∧ (C.loc q = .acc .reset V ∨ C.loc q = .wr V) := by
            intro q; simp [l3, g3_iff]
          have hcurinj : Function.Injective (cur α) := fun a b h => congrArg Prod.fst h
          have hM1fst : M1.map Prod.fst = l1.map (cur α) := by simp [M1, Function.comp_def]
          have hM3fst : M3.map Prod.fst = l3.map (cur α) := by simp [M3, Function.comp_def]
          have hMfst : M.map Prod.fst = (l1 ++ p :: l3).map (cur α) := by
            simp only [M, List.map_append, List.map_cons, hM1fst, hM3fst]
          have hmemM1 : ∀ q, cur α q ∈ M1.map Prod.fst ↔ q ∈ l1 := by
            intro q; rw [hM1fst]; exact List.mem_map_of_injective hcurinj
          have hmemM3 : ∀ q, cur α q ∈ M3.map Prod.fst ↔ q ∈ l3 := by
            intro q; rw [hM3fst]; exact List.mem_map_of_injective hcurinj
          have hmemM : ∀ q, cur α q ∈ M.map Prod.fst ↔ q ∈ l1 ∨ q = p ∨ q ∈ l3 := by
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
              opOf α (cur α q) = some o ∧ cur α q ∉ Lin.map Prod.fst := by
            intro q hq
            obtain ⟨o, ho, h⟩ := (hl1 q).1 hq
            have := hI.st q
            unfold St at this; rw [h] at this
            exact ⟨o, ho, h, this.2.1, this.2.2.2.2.1 rfl⟩
          have hstl3 : ∀ q ∈ l3, opOf α (cur α q) = some .reset ∧
              cur α q ∉ Lin.map Prod.fst := by
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
            rw [linState, List.map_append, ObjSpec.runOps_append]
            change mtasObj.runOps (linState Lin) _ = false
            rw [hLin]
            simp only [M, List.map_append, List.map_cons]
            rw [ObjSpec.runOps_append, runOps_const true true M1 hM1c, ObjSpec.runOps_cons]
            exact runOps_const false false M3 hM3c
          have hrespM1 : ∀ q ∈ l1, linResp (Lin ++ M) (cur α q) = some true := by
            intro q hq
            obtain ⟨-, -, -, -, hnl⟩ := hstl1 q hq
            rw [linResp_append_of_not_mem _ hnl, hLin]
            exact linRespFrom_const _ _ _ _ _ hM1c ((hmemM1 q).2 hq)
          have hrespP : linResp (Lin ++ M) (cur α p) = some false := by
            rw [linResp_append_of_not_mem _ hp2, hLin,
              linRespFrom_append_of_not_mem _ _ _ _ (fun h => hpl1 ((hmemM1 p).1 h)),
              runOps_const true true M1 hM1c]
            simp [linRespFrom]
          have hrespM3 : ∀ q ∈ l3, linResp (Lin ++ M) (cur α q) = some false := by
            intro q hq
            have hqp : q ≠ p := ((hl3 q).1 hq).1
            rw [linResp_append_of_not_mem _ (hstl3 q hq).2, hLin,
              linRespFrom_append_of_not_mem _ _ _ _ (fun h => hl13 q ((hmemM1 q).1 h) hq),
              runOps_const true true M1 hM1c]
            simp only [linRespFrom]
            rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hqp (congrArg Prod.fst h).symm))]
            have := linRespFrom_const (cur α q) false false M3 [] hM3c ((hmemM3 q).2 hq)
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
              rw [hlocp, hpend, cur_append_tau]
              exact ⟨by rw [hp1]; simp, hrespP⟩
            · have hqst := hI.st q
              unfold St at hqst ⊢
              rw [hlocq q hq, hpendq q, cur_append_tau, hV]
              cases hc : C.loc q with
              | idle => rw [hc] at hqst; exact hqst
              | start o =>
                rw [hc] at hqst
                refine ⟨hqst.1, not_mem_append hqst.2.1 ?_, opOf_append_of_opOf _ hqst.2.2⟩
                rw [hmemM]
                rintro (h | h | h)
                · obtain ⟨o', -, h'⟩ := (hl1 q).1 h; rw [hc] at h'; cases h'
                · exact hq h
                · rcases ((hl3 q).1 h).2 with h' | h' <;> rw [hc] at h' <;> cases h'
              | acc o c' =>
                rw [hc] at hqst
                obtain ⟨h1, h2, h3, h4, -, h6⟩ := hqst
                refine ⟨h1, opOf_append_of_opOf _ h2, h3, by omega, fun h => by omega,
                  fun _ => ?_⟩
                rcases Nat.lt_or_eq_of_le h4 with h | rfl
                · exact linResp_append_of_some _ (h6 h)
                · cases o with
                  | tas => exact hrespM1 q ((hl1 q).2 ⟨_, by simp, hc⟩)
                  | read => exact hrespM1 q ((hl1 q).2 ⟨_, by simp, hc⟩)
                  | reset => exact hrespM3 q ((hl3 q).2 ⟨hq, Or.inl hc⟩)
              | wr c' =>
                rw [hc] at hqst
                obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hqst
                refine ⟨h1, opOf_append_of_opOf _ h2, h3, by omega, by rw [hmts]; exact h5,
                  fun h => by omega, fun _ => ?_⟩
                rcases Nat.lt_or_eq_of_le h4 with h | rfl
                · exact linResp_append_of_some _ (h7 h)
                · exact hrespM3 q ((hl3 q).2 ⟨hq, Or.inr hc⟩)
              | retv b =>
                rw [hc] at hqst
                exact ⟨hqst.1, linResp_append_of_some _ hqst.2⟩
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
        refine ⟨hI.lin.append_ret_of_linResp hst.2, by rw [hmem]; exact hI.one,
          by rw [hmem]; exact hI.abs, by rw [hmem]; exact hI.below, by rw [hmem]; exact hI.above,
          fun q => ?_⟩
        by_cases hq : q = p
        · subst hq; unfold St; rw [hloc, Function.update_self, hpend, Function.update_self]
        · simpa using (hI.st q).transfer (M := []) (by rw [hloc, Function.update_of_ne hq])
            (by rw [hpend, Function.update_of_ne hq]) (cur_append_ret_of_ne _ _ (Ne.symm hq))
            (fun o' h => opOf_append_of_opOf _ h) (by simp) (by rw [hmem])
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
