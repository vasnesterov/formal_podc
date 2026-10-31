import Papers.PODC2018.NestingSafeRecoverable.Thm4Basic
import Podc.Computability.Distributed.SharedMemory.NRL.Erase

/-!
# Non-vacuity of the hypotheses of Theorem 4 (sanity check, not a result of the paper)

Theorem 4 (`theorem4`) says that no algorithm whose base objects are read/write-like or
test&set-like is both NRL and wait-free (for one-shot test&set). To check that the two hypotheses
`A.NRL OneShot` and `A.WaitFree OneShot` are not jointly unsatisfiable *in our model* (which would
make Theorem 4 vacuous), we give a recoverable test&set `casTAS P` built from a single
compare&swap object `W` (initially `none`), for any process type `P`:

* `cas`: `W.cas(none, some p)` (the response is ignored);
* `read`: `v ← W.read`;
* `ret`: return `v ≠ some p` (`false` = 0 iff `p` is the winner).

The recovery function restarts at `cas` from any location (re-executing is harmless: the `cas`
fails once somebody has won).

Linearization: the winner is linearized at its successful `cas`; a loser is linearized at its
`read` (a `T&S` on the state `true`, read-only, response `true`); a loser that crashes after its
read and before its response is retracted (`IsLinearization.erase_ro`).

Main statements: `casTAS_nrl`, `casTAS_waitFree`, `casTAS_nrl_waitFree`, and
`casTASObj_not_rw_tas` (the compare&swap object is neither read/write-like nor test&set-like, so
`casTAS` is outside the scope of Theorem 4, as it must be).
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL Cslib.SharedMemory.NRL.Alg

/-- Program locations of `casTAS`. -/
inductive CasTASPC
  | cas
  | read
  | ret
  deriving DecidableEq

variable (P : Type) [DecidableEq P]

/-- The base object of `casTAS`: a compare&swap object over `Option P`, initially `none`. -/
abbrev casTASObj : ObjSpec := casObject (Option P) none

/-- The code of `casTAS`. -/
def casTASAct (p : P) :
    CasTASPC → Option P → Act (fun _ : Unit => casTASObj P) CasTASPC (Option P) Bool
  | .cas, _ => .access () (.cas none (some p)) .read (fun _ => none)
  | .read, _ => .access () .read .ret (fun r => Sum.elim id (fun _ => none) r)
  | .ret, v => .ret (decide (v ≠ some p))

/-- A recoverable test&set from one compare&swap object (sanity check for Theorem 4, not an
algorithm of the paper). -/
abbrev casTAS : Alg P tasObj where
  ι := Unit
  T _ := casTASObj P
  PC := CasTASPC
  V := Option P
  start _ _ := (.cas, none)
  recover _ _ _ := (.cas, none)
  act p _ pc v := casTASAct P p pc v

variable {P}

/-- The value of the compare&swap object. -/
def casTASW (C : (casTAS P).Cfg) : Option P := C.mem ()

/-- `Function.update_self` for an arbitrary decidability instance. -/
lemma nvUpdate_self {ι : Type} {β : ι → Type} (inst : DecidableEq ι) (f : (i : ι) → β i) (i : ι)
    (x : β i) : @Function.update ι β inst f i x i = x := by
  let _ := inst; exact Function.update_self ..

variable (C : (casTAS P).Cfg) {q : P} {o : Unit} {v : Option P}

lemma casTAS_step_cas (h : C.st q = some (o, .cas, v)) :
    casTASW (C.ev (.step q)) = some ((casTASW C).getD q) ∧
    (C.ev (.step q)).st = Function.update C.st q (some (o, .read, none)) ∧
    (C.ev (.step q)).hist = C.hist := by
  rw [ev_step_access C h (i := ()) (op := .cas none (some q)) (pc' := .read)
    (k := fun _ => none) rfl]
  refine ⟨?_, rfl, rfl⟩
  unfold casTASW; dsimp only; rw [nvUpdate_self]
  cases C.mem () <;> simp

lemma casTAS_step_read (h : C.st q = some (o, .read, v)) :
    casTASW (C.ev (.step q)) = casTASW C ∧
    (C.ev (.step q)).st = Function.update C.st q (some (o, .ret, casTASW C)) ∧
    (C.ev (.step q)).hist = C.hist := by
  rw [ev_step_access C h (i := ()) (op := .read) (pc' := .ret)
    (k := fun r => Sum.elim id (fun _ => none) r) rfl]
  refine ⟨?_, rfl, rfl⟩
  unfold casTASW; dsimp only; rw [nvUpdate_self]

lemma casTAS_step_ret (h : C.st q = some (o, .ret, v)) :
    casTASW (C.ev (.step q)) = casTASW C ∧
    (C.ev (.step q)).st = Function.update C.st q none ∧
    (C.ev (.step q)).hist = C.hist ++ [.res q (decide (v ≠ some q))] := by
  rw [ev_step_ret C h (r := decide (v ≠ some q)) rfl]
  exact ⟨rfl, rfl, rfl⟩

lemma casTAS_crash {pc : CasTASPC} (h : C.st q = some (o, pc, v)) :
    casTASW (C.ev (.crash q)) = casTASW C ∧
    (C.ev (.crash q)).st = Function.update C.st q (some (o, .cas, none)) ∧
    (C.ev (.crash q)).hist = C.hist ++ [.crash q, .recover q] := by
  rw [ev_crash_of_some C h]
  exact ⟨rfl, rfl, rfl⟩

lemma casTAS_inv (o : Unit) (h : C.st q = none) :
    casTASW (C.ev (.inv q o)) = casTASW C ∧
    (C.ev (.inv q o)).st = Function.update C.st q (some (o, .cas, none)) ∧
    (C.ev (.inv q o)).hist = C.hist ++ [.inv q o] := by
  rw [ev_inv_of_none C o h]
  exact ⟨rfl, rfl, rfl⟩

/-! ### The linearization invariant -/

/-- The linearization invariant of `casTAS`: while `W = none` nobody has passed its `cas` and
nothing is linearized; once `W = some w`, the winner `w` heads the linearization, every process
that has read `W` holds `some w`, and a loser is linearized iff it has returned or is about to
return. -/
structure casTASInv (C : (casTAS P).Cfg) (L : List (OpId P × tasObj.Op)) : Prop where
  lin : IsLinearization (N C.hist) L
  wf : WFInv C
  os : OneShot (N C.hist)
  idle : casTASW C = none → L = [] ∧ ∀ r x, C.st r = some x → x.2.1 = .cas
  won : ∀ w, casTASW C = some w → (∃ M, L = ((w, 0), ()) :: M) ∧
    ∀ r o pc v, C.st r = some (o, pc, v) → (pc = .ret → v = some w) ∧
      (r ≠ w → ((r, 0) ∈ L.map Prod.fst ↔ pc = .ret))

variable {C}

/-- A pending process has invoked exactly one operation and has not returned. -/
lemma casTAS_pend (hw : WFInv C) (hos : OneShot (N C.hist)) {x} (hq : C.st q = some x) :
    opOf (N C.hist) (q, 0) = some () ∧ ¬ Completed (N C.hist) (q, 0) ∧
      respsOf (N C.hist) q = [] := by
  have h1 := hw.pend q
  have h2 := hos q
  rw [hq] at h1
  simp only [Option.isSome_some, ↓reduceIte] at h1
  have h3 : (respsOf (N C.hist) q).length = 0 := by omega
  refine ⟨?_, ?_, List.length_eq_zero_iff.1 h3⟩
  · simp only [opOf]
    rw [List.getElem?_eq_getElem (by omega)]
  · simp [Completed, h3]

lemma casTAS_not_mem {L : List (OpId P × tasObj.Op)} (hL : IsLinearization (N C.hist) L)
    (h : opsOf (N C.hist) q = []) : (q, 0) ∉ L.map Prod.fst := fun hm => by
  have := hL.mem_invoked hm
  simp [Invoked, h] at this

lemma nv_tas_runOps_true (l : List Unit) : tasObj.runOps true l = true := by
  induction l with
  | nil => rfl
  | cons _ l ih => exact ih

lemma nv_tas_runOps_cons (u : Unit) (l : List Unit) : tasObj.runOps false (u :: l) = true :=
  nv_tas_runOps_true l

omit [DecidableEq P] in
lemma nv_split {M : List (OpId P × tasObj.Op)} {x : OpId P} (h : x ∈ M.map Prod.fst) :
    ∃ M₁ M₂, M = M₁ ++ (x, ()) :: M₂ := by
  obtain ⟨⟨y, u⟩, hy, rfl⟩ := List.mem_map.1 h
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hy
  exact ⟨M₁, M₂, rfl⟩

omit [DecidableEq P] in
lemma nv_mem_middle {x y : OpId P} (hxy : x ≠ y) (M₁ M₂ : List (OpId P × tasObj.Op)) (u : Unit) :
    x ∈ (M₁ ++ (y, u) :: M₂).map Prod.fst ↔ x ∈ (M₁ ++ M₂).map Prod.fst := by
  simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons, hxy, false_or]

omit [DecidableEq P] in
lemma nv_mem_concat {x y : OpId P} (hxy : x ≠ y) (M : List (OpId P × tasObj.Op)) (u : Unit) :
    x ∈ (M ++ [(y, u)]).map Prod.fst ↔ x ∈ M.map Prod.fst := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, hxy,
    List.not_mem_nil, or_false]

/-! ### One-step preservation of the invariant -/

variable {L : List (OpId P × tasObj.Op)}

lemma casTASInv.ev_inv (h : casTASInv C L) (o : Unit) (hs : C.st q = none)
    (hos : OneShot (N (C.ev (.inv q o)).hist)) : casTASInv (C.ev (.inv q o)) L := by
  obtain ⟨hW, hst, hH⟩ := casTAS_inv C o hs
  have hq0 : opsOf (N C.hist) q = [] := by
    have := hos q
    rw [hH, N_append, N_inv, opsOf_append] at this
    have h1 : opsOf [(Label.inv q o : Label P tasObj)] q = [o] := by simp [opsOf, Label.invOf]
    rw [h1, List.length_append, List.length_singleton] at this
    exact List.length_eq_zero_iff.1 (by omega)
  have hqL := casTAS_not_mem h.lin hq0
  refine ⟨?_, h.wf.ev _, hos, ?_, ?_⟩
  · rw [hH, N_append, N_inv]; exact h.lin.append_inv q o
  · intro hw
    rw [hW] at hw
    obtain ⟨h1, h2⟩ := h.idle hw
    refine ⟨h1, fun r x hr => ?_⟩
    rw [hst] at hr
    by_cases hrq : r = q
    · subst hrq; simp at hr; subst hr; rfl
    · rw [Function.update_of_ne hrq] at hr; exact h2 r x hr
  · intro w hw
    rw [hW] at hw
    obtain ⟨h1, h2⟩ := h.won w hw
    refine ⟨h1, fun r o' pc v hr => ?_⟩
    rw [hst] at hr
    by_cases hrq : r = q
    · subst hrq
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl, rfl⟩ := hr
      simp [hqL]
    · rw [Function.update_of_ne hrq] at hr; exact h2 r o' pc v hr

lemma casTASInv.ev_cas (h : casTASInv C L) (hs : C.st q = some (o, .cas, v)) :
    ∃ L', casTASInv (C.ev (.step q)) L' := by
  obtain ⟨hW, hst, hH⟩ := casTAS_step_cas C hs
  obtain ⟨hop, hnc, -⟩ := casTAS_pend h.wf h.os hs
  cases hm : casTASW C with
  | none =>
    obtain ⟨hL, h2⟩ := h.idle hm
    subst hL
    refine ⟨[((q, 0), ())], ?_, h.wf.ev _, ?_, ?_, ?_⟩
    · rw [hH]; simpa using h.lin.push hop (by simp) hnc
    · rw [hH]; exact h.os
    · intro hw; rw [hW] at hw; simp at hw
    · intro w hw
      rw [hW, hm] at hw
      simp only [Option.getD_none, Option.some.injEq] at hw
      subst hw
      refine ⟨⟨[], rfl⟩, fun r o' pc v' hr => ?_⟩
      rw [hst] at hr
      by_cases hrq : r = q
      · subst hrq
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl, rfl⟩ := hr
        simp
      · rw [Function.update_of_ne hrq] at hr
        have := h2 r _ hr
        simp only at this
        subst this
        simp [hrq]
  | some w =>
    obtain ⟨h1, h2⟩ := h.won w hm
    refine ⟨L, ?_, h.wf.ev _, ?_, ?_, ?_⟩
    · rw [hH]; exact h.lin
    · rw [hH]; exact h.os
    · intro hw; rw [hW] at hw; simp at hw
    · intro w' hw
      rw [hW, hm] at hw
      simp only [Option.getD_some, Option.some.injEq] at hw
      subst hw
      refine ⟨h1, fun r o' pc v' hr => ?_⟩
      rw [hst] at hr
      by_cases hrq : r = q
      · subst hrq
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl, rfl⟩ := hr
        have := (h2 r o .cas v hs).2
        simp only [reduceCtorEq, iff_false] at this
        simpa using this
      · rw [Function.update_of_ne hrq] at hr; exact h2 r o' pc v' hr

lemma casTASInv.ev_read (h : casTASInv C L) (hs : C.st q = some (o, .read, v)) :
    ∃ L', casTASInv (C.ev (.step q)) L' := by
  obtain ⟨hW, hst, hH⟩ := casTAS_step_read C hs
  obtain ⟨hop, hnc, -⟩ := casTAS_pend h.wf h.os hs
  cases hm : casTASW C with
  | none => have := (h.idle hm).2 q _ hs; simp at this
  | some w =>
    obtain ⟨⟨M, hL⟩, h2⟩ := h.won w hm
    have hidle : casTASW (C.ev (.step q)) = none → False := by rw [hW, hm]; simp
    by_cases hqw : q = w
    · refine ⟨L, ?_, h.wf.ev _, ?_, fun hw => (hidle hw).elim, ?_⟩
      · rw [hH]; exact h.lin
      · rw [hH]; exact h.os
      · intro w' hw
        rw [hW, hm] at hw
        cases hw
        refine ⟨⟨M, hL⟩, fun r o' pc v' hr => ?_⟩
        rw [hst] at hr
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨-, rfl, rfl⟩ := hr
          simp [hm, hqw]
        · rw [Function.update_of_ne hrq] at hr; exact h2 r o' pc v' hr
    · have hqL : (q, 0) ∉ L.map Prod.fst := by
        have := (h2 q o .read v hs).2 hqw; simpa using this
      refine ⟨L ++ [((q, 0), ())], ?_, h.wf.ev _, ?_, fun hw => (hidle hw).elim, ?_⟩
      · rw [hH]; exact h.lin.push hop hqL hnc
      · rw [hH]; exact h.os
      · intro w' hw
        rw [hW, hm] at hw
        cases hw
        refine ⟨⟨M ++ [((q, 0), ())], by simp [hL]⟩, fun r o' pc v' hr => ?_⟩
        rw [hst] at hr
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨-, rfl, rfl⟩ := hr
          simp [hm]
        · rw [Function.update_of_ne hrq] at hr
          have := h2 r o' pc v' hr
          rw [nv_mem_concat (by simpa using hrq)]
          exact this

lemma casTASInv.ev_ret (h : casTASInv C L) (hs : C.st q = some (o, .ret, v))
    (hos : OneShot (N (C.ev (.step q)).hist)) : ∃ L', casTASInv (C.ev (.step q)) L' := by
  obtain ⟨hW, hst, hH⟩ := casTAS_step_ret C hs
  obtain ⟨-, -, hres⟩ := casTAS_pend h.wf h.os hs
  cases hm : casTASW C with
  | none => have := (h.idle hm).2 q _ hs; simp at this
  | some w =>
    obtain ⟨⟨M, hL⟩, h2⟩ := h.won w hm
    have hv : v = some w := (h2 q o .ret v hs).1 rfl
    subst hv
    refine ⟨L, ?_, h.wf.ev _, hos, ?_, ?_⟩
    · rw [hH, N_append, N_res]
      by_cases hqw : q = w
      · subst hqw
        refine h.lin.append_ret [] M () (by simp [hL, hres]) ?_
        simp; rfl
      · have hq' := ((h2 q o .ret _ hs).2 hqw).2 rfl
        rw [hL, List.map_cons, List.mem_cons] at hq'
        obtain ⟨M₁, M₂, rfl⟩ := nv_split (hq'.resolve_left (by simp [hqw]))
        refine h.lin.append_ret (((w, 0), ()) :: M₁) M₂ () (by simp [hL, hres]) ?_
        simp [Ne.symm hqw]; exact nv_tas_runOps_cons _ _
    · intro hw; rw [hW, hm] at hw; simp at hw
    · intro w' hw
      rw [hW, hm] at hw
      cases hw
      refine ⟨⟨M, hL⟩, fun r o' pc v' hr => ?_⟩
      rw [hst] at hr
      by_cases hrq : r = q
      · subst hrq; simp at hr
      · rw [Function.update_of_ne hrq] at hr; exact h2 r o' pc v' hr

lemma casTASInv.ev_crash (h : casTASInv C L) {pc : CasTASPC} (hs : C.st q = some (o, pc, v)) :
    ∃ L', casTASInv (C.ev (.crash q)) L' := by
  obtain ⟨hW, hst, hH⟩ := casTAS_crash C hs
  obtain ⟨-, hnc, -⟩ := casTAS_pend h.wf h.os hs
  have hN : N (C.ev (.crash q)).hist = N C.hist := by
    rw [hH, N_append, N_crash_rec, List.append_nil]
  cases hm : casTASW C with
  | none =>
    obtain ⟨hL, h2⟩ := h.idle hm
    refine ⟨L, ?_, h.wf.ev _, ?_, ?_, ?_⟩
    · rw [hN]; exact h.lin
    · rw [hN]; exact h.os
    · intro _
      refine ⟨hL, fun r x hr => ?_⟩
      rw [hst] at hr
      by_cases hrq : r = q
      · subst hrq; simp at hr; subst hr; rfl
      · rw [Function.update_of_ne hrq] at hr; exact h2 r x hr
    · intro w hw; rw [hW, hm] at hw; simp at hw
  | some w =>
    obtain ⟨⟨M, hL⟩, h2⟩ := h.won w hm
    have hidle : casTASW (C.ev (.crash q)) = none → False := by rw [hW, hm]; simp
    by_cases hkeep : q = w ∨ pc ≠ .ret
    · have hqL : q ≠ w → (q, 0) ∉ L.map Prod.fst := fun hqw hmem =>
        hkeep.elim hqw (fun hpc => hpc (((h2 q o pc v hs).2 hqw).1 hmem))
      refine ⟨L, ?_, h.wf.ev _, ?_, fun hw => (hidle hw).elim, ?_⟩
      · rw [hN]; exact h.lin
      · rw [hN]; exact h.os
      · intro w' hw
        rw [hW, hm] at hw
        cases hw
        refine ⟨⟨M, hL⟩, fun r o' pc' v' hr => ?_⟩
        rw [hst] at hr
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨-, rfl, rfl⟩ := hr
          simpa using hqL
        · rw [Function.update_of_ne hrq] at hr; exact h2 r o' pc' v' hr
    · simp only [not_or, not_not] at hkeep
      obtain ⟨hqw, rfl⟩ := hkeep
      have hq' := ((h2 q o .ret v hs).2 hqw).2 rfl
      rw [hL, List.map_cons, List.mem_cons] at hq'
      obtain ⟨M₁, M₂, rfl⟩ := nv_split (hq'.resolve_left (by simp [hqw]))
      have hnd := h.lin.nodup
      rw [hL, List.map_cons, List.nodup_cons, List.map_append, List.map_cons] at hnd
      have hq2 : (q, 0) ∉ (M₁ ++ M₂).map Prod.fst := by
        have := (List.nodup_cons.1 (List.nodup_middle.1 hnd.2)).1
        simpa using this
      refine ⟨((w, 0), ()) :: (M₁ ++ M₂), ?_, h.wf.ev _, ?_, fun hw => (hidle hw).elim, ?_⟩
      · rw [hN]
        have hlin := h.lin
        rw [show L = (((w, 0), ()) :: M₁) ++ ((q, 0), ()) :: M₂ by simp [hL]] at hlin
        simpa using hlin.erase_ro hnc (by simp; exact nv_tas_runOps_cons _ _)
      · rw [hN]; exact h.os
      · intro w' hw
        rw [hW, hm] at hw
        cases hw
        refine ⟨⟨M₁ ++ M₂, rfl⟩, fun r o' pc' v' hr => ?_⟩
        rw [hst] at hr
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨-, rfl, rfl⟩ := hr
          refine ⟨by simp, fun _ => ?_⟩
          simp only [List.map_cons, List.mem_cons, reduceCtorEq, iff_false, not_or]
          exact ⟨by simpa using hqw, hq2⟩
        · rw [Function.update_of_ne hrq] at hr
          have := h2 r o' pc' v' hr
          rw [hL, List.map_cons, List.mem_cons, nv_mem_middle (by simpa using hrq)] at this
          simpa only [List.map_cons, List.mem_cons] using this

lemma casTASInv.ev (h : casTASInv C L) (e : Ev P tasObj) (hos : OneShot (N (C.ev e).hist)) :
    ∃ L', casTASInv (C.ev e) L' := by
  rcases e with ⟨q, o⟩ | q | q
  · rcases hs : C.st q with _ | x
    · exact ⟨L, h.ev_inv o hs hos⟩
    · rw [ev_inv_of_some C o hs]; exact ⟨L, h⟩
  · rcases hs : C.st q with _ | ⟨o, pc, v⟩
    · rw [ev_step_of_none C hs]; exact ⟨L, h⟩
    · cases pc with
      | cas => exact h.ev_cas hs
      | read => exact h.ev_read hs
      | ret => exact h.ev_ret hs hos
  · rcases hs : C.st q with _ | ⟨o, pc, v⟩
    · rw [ev_crash_of_none C hs]; exact ⟨L, h⟩
    · exact h.ev_crash hs

lemma casTASInv_init : casTASInv (casTAS P).init [] where
  lin := isLinearization_nil
  wf := wfInv_init
  os := by intro x; simp [init]
  idle _ := ⟨rfl, fun r x hr => by simp [init] at hr⟩
  won w hw := by simp [casTASW, init] at hw

lemma nv_oneShot_of_ev {C : (casTAS P).Cfg} {e : Ev P tasObj} (h : OneShot (N (C.ev e).hist)) :
    OneShot (N C.hist) := by
  obtain ⟨l, hl⟩ := ev_hist C e
  intro x
  have := h x
  rw [hl, N_append, opsOf_append, List.length_append] at this
  omega

lemma casTASInv_run (es : List (Ev P tasObj))
    (hos : OneShot (N ((casTAS P).init.run es).hist)) :
    ∃ L, casTASInv ((casTAS P).init.run es) L := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨[], casTASInv_init⟩
  | append_singleton es e ih =>
    rw [Cfg.run_concat] at hos ⊢
    obtain ⟨L, hL⟩ := ih (nv_oneShot_of_ev hos)
    exact hL.ev e hos

/-- **Sanity check (not a result of the paper)**: the compare&swap-based test&set `casTAS`
satisfies nesting-safe recoverable linearizability for one-shot test&set. -/
theorem casTAS_nrl : (casTAS P).NRL OneShot := by
  rw [nrl_iff]
  intro es hes
  obtain ⟨L, hL⟩ := casTASInv_run es hes
  exact ⟨L, hL.lin⟩

/-! ### Wait-freedom -/

/-- Remaining own steps before the response, by program location. -/
def nvRk : CasTASPC → ℕ
  | .cas => 2
  | .read => 1
  | .ret => 0

/-- Remaining own steps of `p` in `D` (`0` if `p` is idle). -/
def nvR (D : (casTAS P).Cfg) (p : P) : ℕ :=
  match D.st p with
  | some x => nvRk x.2.1
  | none => 0

lemma nvR_of_eq {D : (casTAS P).Cfg} {p : P} {o : Unit} {pc : CasTASPC} {v : Option P}
    (h : D.st p = some (o, pc, v)) : nvR D p = nvRk pc := by
  simp [nvR, h]

/-- One event does not increase the remaining own steps of a pending process that does not
crash, and a step of the process decreases them (or completes the operation). -/
lemma nvR_ev {D : (casTAS P).Cfg} {p : P} {e : Ev P tasObj} (he : e ≠ .crash p)
    {o : Unit} {pc : CasTASPC} {v : Option P} (hD : D.st p = some (o, pc, v))
    (hne : (D.ev e).st p ≠ none) :
    nvR (D.ev e) p ≤ nvR D p ∧ (e = .step p → nvR (D.ev e) p < nvR D p) := by
  rw [nvR_of_eq hD]
  rcases e with ⟨q, o'⟩ | q | q
  · have hst : (D.ev (.inv q o')).st p = D.st p := by
      by_cases hqp : q = p
      · subst hqp; rw [ev_inv_of_some D o' hD]
      · rcases hq : D.st q with _ | x
        · rw [ev_inv_of_none D o' hq]; simp [Ne.symm hqp]
        · rw [ev_inv_of_some D o' hq]
    rw [nvR, hst, hD]
    exact ⟨le_rfl, fun h => by cases h⟩
  · by_cases hqp : q = p
    · subst hqp
      cases pc with
      | cas =>
        obtain ⟨-, hst, -⟩ := casTAS_step_cas D hD
        simp [nvR, hst, nvRk]
      | read =>
        obtain ⟨-, hst, -⟩ := casTAS_step_read D hD
        simp [nvR, hst, nvRk]
      | ret =>
        obtain ⟨-, hst, -⟩ := casTAS_step_ret D hD
        simp [hst] at hne
    · rw [nvR, ev_step_st_ne (Ne.symm hqp), hD]
      exact ⟨le_rfl, fun h => by cases h; exact absurd rfl hqp⟩
  · have hqp : q ≠ p := by rintro rfl; exact he rfl
    rw [nvR, ev_crash_st_ne (Ne.symm hqp), hD]
    exact ⟨le_rfl, fun h => by cases h⟩

omit [DecidableEq P] in
lemma nv_pre_succ (e : ℕ → Ev P tasObj) (n : ℕ) : pre e (n + 1) = pre e n ++ [e n] := by
  simp [pre, List.range_succ]

/-- **Sanity check (not a result of the paper)**: `casTAS` is wait-free (operations and
recovery): after its last crash a process returns within three own steps. -/
theorem casTAS_waitFree : (casTAS P).WaitFree OneShot := by
  intro es e p _ _ hcr hinf
  set D : ℕ → (casTAS P).Cfg := fun n => ((casTAS P).init.run es).run (pre e n) with hD
  have hDs : ∀ n, D (n + 1) = (D n).ev (e n) := fun n => by
    simp only [hD, nv_pre_succ, Cfg.run_concat]
  by_contra hall
  simp only [not_exists] at hall
  have hall' : ∀ n, (D n).st p ≠ none := hall
  have hstep : ∀ n, nvR (D (n + 1)) p ≤ nvR (D n) p ∧
      (e n = .step p → nvR (D (n + 1)) p < nvR (D n) p) := by
    intro n
    obtain ⟨⟨o, pc, v⟩, hx⟩ := Option.ne_none_iff_exists'.1 (hall' n)
    rw [hDs]
    exact nvR_ev (hcr n) hx (by rw [← hDs]; exact hall' (n + 1))
  have hmono : ∀ m k, m ≤ k → nvR (D k) p ≤ nvR (D m) p := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (hstep k).1.trans ih
  have key : ∀ j m, nvR (D m) p ≤ j → False := by
    intro j
    induction j with
    | zero =>
      intro m hm
      obtain ⟨n, hmn, hn⟩ := hinf m
      have := (hstep n).2 hn
      have := hmono m n hmn
      omega
    | succ j ih =>
      intro m hm
      obtain ⟨n, hmn, hn⟩ := hinf m
      have h1 := (hstep n).2 hn
      have h2 := hmono m n hmn
      exact ih (n + 1) (by omega)
  exact key _ 0 le_rfl

/-- **Sanity check (not a result of the paper)**: the hypotheses `A.NRL OneShot` and
`A.WaitFree OneShot` of `theorem4` are jointly satisfiable once a base object outside the
read/write and test&set classes (here one compare&swap object) is allowed. -/
theorem casTAS_nrl_waitFree : (casTAS P).NRL OneShot ∧ (casTAS P).WaitFree OneShot :=
  ⟨casTAS_nrl, casTAS_waitFree⟩

/-- The compare&swap base object of `casTAS` is neither read/write-like nor test&set-like (as
soon as there is a process), so `casTAS` is not a counterexample to `theorem4`. -/
theorem casTASObj_not_rw_tas (p : P) :
    ¬ ((casTASObj P).RWLike ∨ (casTASObj P).TASLike) := by
  rintro (h | ⟨s₁, h⟩)
  · rcases h (.cas none (some p)) with h | h
    · have := h none
      simp at this
    · have := h none (some p)
      simp at this
  · have h1 := h (some p) .read
    have h2 := h none .read
    simp only at h1 h2
    rw [← h2] at h1
    simp at h1

end Podc.NestingSafeRecoverable
