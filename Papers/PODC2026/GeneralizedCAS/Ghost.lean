import Papers.PODC2026.GeneralizedCAS.Defs

/-!
# Algorithm 1: a non-dependent view of the memory, the effect of a step, ghost variables

* `Mem` is a plain record view of the base objects (`Cfg.M`), and `effect l M` computes the
  effect of one step of a process in local state `l` (`step_tau_iff`).
* `Ghost` holds the ghost variables used in the proofs; they do not influence the algorithm:
  - `ts τ` — the operation instance (process, index, operation) that obtained timestamp `τ`;
  - `lin` — the linearization: operations in the order of their successful CAS on `S`
    (line 13), the linearization points of the paper (Theorem B.3.1);
  - `k p` — the number of completed operations of `p`;
  - `it p`, `ns p` — the number of complete loop iterations / of steps of `p` in its current
    operation;
  - `clock`, `lt p c` — the current time and the time of the last step of `p` at line `c`;
  - `wd τ` — how many times the owner of `τ` executed line 8 or 15 for `τ` while `τ` was done.
* `arun α` runs the algorithm with the ghost variables along `α` (`arun_fst`, `exists_arun`).
-/

set_option linter.unusedSimpArgs false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]

variable (T) in
/-- A record view of the shared memory. -/
@[ext] structure Mem where
  cnt : ℕ
  A : AVal T.Op
  S : SVal T.State T.Resp
  mm : ℕ
  cell : Ptr → CellVal T.Resp

variable (T P) in
/-- Configurations of Algorithm 1. -/
abbrev Cfg := Config T (base T) P (Loc T)

/-- The record view of the base objects. -/
abbrev view (m : (i : Obj) → (base T i).State) : Mem T :=
  ⟨m .C, m .A, m .S, m .MM, fun x => m (.cell x)⟩

/-- The memory of a configuration. -/
def Cfg.M (C : Cfg T P) : Mem T := view C.mem

open Classical in
/-- Compare-and-swap on a cell value. -/
noncomputable def cellCAS (c old new : CellVal T.Resp) : CellVal T.Resp := if c = old then new else c

open Classical in
/-- The program counter after line 5 (the test of line 5, or the return of line 16). -/
noncomputable def pc5 (l : Loc T) (M : Mem T) : PC T.Resp :=
  if M.cell l.me = ⟨l.t, .null⟩ then .l6 else
  match (M.cell l.me).resp with
  | .val r => .l16 r
  | _ => .l5

open Classical in
/-- The effect of one step of a process in local state `l` on the memory and on `l`. -/
noncomputable def effect (l : Loc T) (M : Mem T) : Mem T × Loc T :=
  match l.pc with
  | .l2 => ({ M with mm := M.mm + 1 }, { l with ptr := some (M.mm : Ptr), pc := .l3 })
  | .l3 => ({ M with cnt := M.cnt + 1 }, { l with t := M.cnt, pc := .l4 })
  | .l4 => ({ M with cell := Function.update M.cell l.me ⟨l.t, .null⟩ }, { l with pc := .l5 })
  | .l5 => (M, { l with pc := pc5 l M })
  | .l6 => (M, { l with snap := M.S, pc := .l7 })
  | .l7 =>
    let c := cellCAS (M.cell l.snap.ptr) ⟨l.snap.time, .null⟩ ⟨l.snap.time, l.snap.resp⟩
    ({ M with cell := Function.update M.cell l.snap.ptr c }, { l with pc := .l8 })
  | .l8 => ({ M with A := if l.mine < M.A then l.mine else M.A }, { l with pc := .l9 })
  | .l9 => (M, { l with ann := M.A, pc := .l10 })
  | .l10 => (M, { l with pc := if M.cell l.ann.ptr = ⟨l.ann.time, .null⟩ then .l13 else .l15 })
  | .l13 => ({ M with S := if M.S = l.snap then l.newS else M.S }, { l with pc := .l5 })
  | .l15 => ({ M with A := if M.A = l.ann then l.mine else M.A }, { l with pc := .l5 })
  | .l16 _ => (M, l)

/-- A process in local state `l` takes memory steps (not a response). -/
def Loc.IsMem (l : Loc T) : Prop := ∀ r, l.pc ≠ .l16 r

variable (cellInit : ℕ → CellVal T.Resp)

lemma act_l16 {l : Loc T} {r : T.Resp} (h : l.pc = .l16 r) :
    act T l = .ret r { l with pc := .l2 } := by
  simp only [act, h]

section view
variable (m : (i : Obj) → (base T i).State)

@[simp] lemma view_update_C (v : ℕ) : view (Function.update m .C v) = { view m with cnt := v } := by
  ext <;> simp [view, Function.update_of_ne]
@[simp] lemma view_update_A (v : AVal T.Op) :
    view (Function.update m .A v) = { view m with A := v } := by
  ext <;> simp [view, Function.update_of_ne]
@[simp] lemma view_update_S (v : SVal T.State T.Resp) :
    view (Function.update m .S v) = { view m with S := v } := by
  ext <;> simp [view, Function.update_of_ne]
@[simp] lemma view_update_MM (v : ℕ) :
    view (Function.update m .MM v) = { view m with mm := v } := by
  ext <;> simp [view, Function.update_of_ne]
@[simp] lemma view_update_cell (x : Ptr) (v : CellVal T.Resp) :
    view (Function.update m (.cell x) v) = { view m with cell := Function.update (view m).cell x v } := by
  refine Mem.ext ?_ ?_ ?_ ?_ ?_
  · simp [view, Function.update_of_ne]
  · simp [view, Function.update_of_ne]
  · simp [view, Function.update_of_ne]
  · simp [view, Function.update_of_ne]
  · funext y
    by_cases hy : y = x
    · subst hy; simp [view]
    · simp only [view]
      rw [Function.update_of_ne (by simpa using hy), Function.update_of_ne hy]
end view

/-- A memory step of a process. -/
lemma step_tau_eff {C C' : Cfg T P} {p : P} (h : (alg T P cellInit).step C (.tau p) = some C') :
      C.pend p ≠ none ∧ (C.loc p).IsMem ∧ C'.pend = C.pend ∧
      C'.M = (effect (C.loc p) C.M).1 ∧
      C'.loc = Function.update C.loc p (effect (C.loc p) C.M).2 := by
  classical
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  refine ⟨hp, ?_, hpend, ?_⟩
  · intro r hr
    simp only [alg, act_l16 hr] at hact
    cases hact
  simp only [Cfg.M]; rw [hmem, hloc]
  simp only [alg] at hact
  cases hpc : (C.loc p).pc <;> simp only [act, hpc] at hact <;> cases hact <;>
    simp only [effect, hpc, view_update_C, view_update_A, view_update_S, view_update_MM,
      view_update_cell, Function.update_eq_self, Cmp.test, decide_eq_true_eq, pc5, cellCAS] <;>
    refine ⟨?_, ?_⟩ <;> first | trivial | rfl | (split_ifs <;> simp_all)
  all_goals (congr 1; rcases hr : (C.mem (Obj.cell (C.loc p).me)).resp with _ | _ | r <;> simp [hr])

/-- A response step of a process. -/
lemma step_ret_eff {C C' : Cfg T P} {p : P} {r : T.Resp}
    (h : (alg T P cellInit).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ (C.loc p).pc = .l16 r ∧ C'.pend = Function.update C.pend p none ∧
      C'.mem = C.mem ∧ C'.loc = Function.update C.loc p { (C.loc p) with pc := .l2 } := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine ⟨hp, ?_, hpend, hmem, ?_⟩
  · simp only [alg] at hact
    unfold act at hact
    split at hact <;> first | (cases hact; done) | (cases hact; assumption)
  · rw [hloc]; congr 1
    simp only [alg] at hact
    unfold act at hact
    split at hact <;> first | (cases hact; done) | (cases hact; rfl)

/-- An invocation step. -/
lemma step_inv_eff {C C' : Cfg T P} {p : P} {o : T.Op}
    (h : (alg T P cellInit).step C (.inv p o) = some C') :
    C.pend p = none ∧ C'.pend = Function.update C.pend p (some o) ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc p ((C.loc p).invoke o) := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  exact ⟨hp, hpend, hmem, by rw [hloc]; rfl⟩

/-! ## Ghost variables -/

variable (T P) in
/-- The ghost variables. -/
structure Ghost where
  /-- `ts τ = some (q, k, o)`: the `k`-th operation `o` of `q` obtained timestamp `τ`. -/
  ts : ℕ → Option (P × ℕ × T.Op)
  /-- The linearization (operations in the order of their successful CAS on `S`). -/
  lin : List (OpId P × T.Op)
  /-- Number of completed operations. -/
  k : P → ℕ
  /-- Number of complete iterations of the loop (executions of line 13 or 15) in the current
  operation. -/
  it : P → ℕ
  /-- Number of (memory) steps in the current operation. -/
  ns : P → ℕ
  /-- Number of executions of line 8 or 15 for `τ` by its owner while `τ` is done. -/
  wd : ℕ → ℕ
  /-- The number of steps taken so far (the current "time"). -/
  clock : ℕ
  /-- `lt p c`: the time of the last step of `p` executed at program counter `c`. -/
  lt : P → PC T.Resp → ℕ

/-- The owner `q` of an operation with index `k` has executed line 4 for it. -/
def WrittenAt (loc : P → Loc T) (G : Ghost T P) (q : P) (k : ℕ) : Prop :=
  k < G.k q ∨ (loc q).pc ≠ .l4

/-- **Definition B.1.7 (done)**, as a property of the current state: `τ` is `Noop`'s
timestamp `0`, or the owner of `τ` has written its cell for `τ` and the cell no longer contains
`(τ, Null)`. (Monotone in time, see `Invariant.lean`.) -/
def DoneL (loc : P → Loc T) (M : Mem T) (G : Ghost T P) (τ : ℕ) : Prop :=
  τ = 0 ∨ ∃ q k o, G.ts τ = some (q, k, o) ∧ WrittenAt loc G q k ∧
    M.cell (loc q).me ≠ ⟨τ, .null⟩

/-- `DoneL` in a configuration. -/
abbrev Done (C : Cfg T P) (G : Ghost T P) (τ : ℕ) : Prop := DoneL C.loc C.M G τ

open Classical in
/-- How a step changes the ghost variables. -/
noncomputable def augStep (C : Cfg T P) : Label P T → Ghost T P → Ghost T P
  | .inv p _, G =>
    { G with
      it := Function.update G.it p 0
      ns := Function.update G.ns p 0
      clock := G.clock + 1 }
  | .ret p _, G => { G with k := Function.update G.k p (G.k p + 1), clock := G.clock + 1 }
  | .tau p, G =>
    let G₁ :=
      { G with
        ns := Function.update G.ns p (G.ns p + 1)
        clock := G.clock + 1
        lt := Function.update G.lt p (Function.update (G.lt p) (C.loc p).pc G.clock) }
    let G₂ := { G₁ with it := Function.update G.it p (G.it p + 1) }
    match (C.loc p).pc with
    | .l3 => { G₁ with ts := Function.update G.ts C.M.cnt ((C.pend p).map fun o => (p, G.k p, o)) }
    | .l8 => if Done C G (C.loc p).t then
        { G₁ with wd := Function.update G.wd (C.loc p).t (G.wd (C.loc p).t + 1) } else G₁
    | .l15 => if Done C G (C.loc p).t then
        { G₂ with wd := Function.update G.wd (C.loc p).t (G.wd (C.loc p).t + 1) } else G₂
    | .l13 =>
      if C.M.S = (C.loc p).snap then
        match G.ts (C.loc p).ann.time with
        | some (q, k, o) => { G₂ with lin := G.lin ++ [((q, k), o)] }
        | none => G₂
      else G₂
    | _ => G₁

variable (T P) in
/-- Initial ghost variables. -/
def ginit : Ghost T P :=
  ⟨fun _ => none, [], fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ _ => 0⟩

/-- Running the algorithm with ghost variables. -/
noncomputable def arunFrom : Cfg T P × Ghost T P → List (Label P T) → Option (Cfg T P × Ghost T P)
  | c, [] => some c
  | c, ℓ :: α => ((alg T P cellInit).step c.1 ℓ).bind
      (fun C' => arunFrom (C', augStep c.1 ℓ c.2) α)

/-- The algorithm with ghost variables run along `α`. -/
noncomputable def arun (α : List (Label P T)) : Option (Cfg T P × Ghost T P) :=
  arunFrom cellInit ((alg T P cellInit).initCfg, ginit T P) α

lemma arunFrom_append (c : Cfg T P × Ghost T P) (α β : List (Label P T)) :
    arunFrom cellInit c (α ++ β) =
      (arunFrom cellInit c α).bind (fun c' => arunFrom cellInit c' β) := by
  induction α generalizing c with
  | nil => simp [arunFrom]
  | cons ℓ α ih =>
    simp only [List.cons_append, arunFrom, ih]
    cases (alg T P cellInit).step c.1 ℓ <;> simp

lemma arun_concat (α : List (Label P T)) (ℓ : Label P T) :
    arun cellInit (α ++ [ℓ]) = (arun cellInit α).bind (fun c =>
      ((alg T P cellInit).step c.1 ℓ).map (fun C' => (C', augStep c.1 ℓ c.2))) := by
  simp only [arun, arunFrom_append]
  congr 1; funext c
  simp only [arunFrom]
  cases (alg T P cellInit).step c.1 ℓ <;> simp

/-- Induction principle for the augmented runs. -/
lemma arun_induction {Q : List (Label P T) → Cfg T P → Ghost T P → Prop}
    (h0 : Q [] (alg T P cellInit).initCfg (ginit T P))
    (hs : ∀ α C G ℓ C', arun cellInit α = some (C, G) → Q α C G →
      (alg T P cellInit).step C ℓ = some C' → Q (α ++ [ℓ]) C' (augStep C ℓ G))
    {α : List (Label P T)} {C : Cfg T P} {G : Ghost T P}
    (h : arun cellInit α = some (C, G)) : Q α C G := by
  induction α using List.reverseRecOn generalizing C G with
  | nil => simp only [arun, arunFrom, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; exact h0
  | append_singleton α ℓ ih =>
    rw [arun_concat] at h
    cases hα : arun cellInit α with
    | none => simp [hα] at h
    | some c =>
      obtain ⟨C₀, G₀⟩ := c
      simp only [hα, Option.bind_some] at h
      cases hst : (alg T P cellInit).step C₀ ℓ with
      | none => simp [hst] at h
      | some C' =>
        simp only [hst, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hs α C₀ G₀ ℓ C' hα (ih hα) hst

lemma arun_fst {α : List (Label P T)} {C : Cfg T P} {G : Ghost T P}
    (h : arun cellInit α = some (C, G)) : (alg T P cellInit).run α = some C :=
  arun_induction cellInit (Q := fun α C _ => (alg T P cellInit).run α = some C) rfl
    (fun α C G ℓ C' _ hr hst => by rw [Impl.run_concat, hr]; exact hst) h

lemma exists_arun {α : List (Label P T)} {C : Cfg T P}
    (h : (alg T P cellInit).run α = some C) : ∃ G, arun cellInit α = some (C, G) := by
  induction α using List.reverseRecOn generalizing C with
  | nil => exact ⟨ginit T P, by simp only [Impl.run_nil, Option.some.injEq] at h; subst h; rfl⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at h
    cases hα : (alg T P cellInit).run α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some] at h
      obtain ⟨G₀, hG⟩ := ih hα
      exact ⟨augStep C₀ ℓ G₀, by rw [arun_concat, hG]; simp [h]⟩

end Podc.GeneralizedCAS
