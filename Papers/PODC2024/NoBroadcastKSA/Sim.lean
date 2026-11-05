import Papers.PODC2024.NoBroadcastKSA.Camp

/-!
# The upper layer of the adversarial executions: simulating copies of `A` on top of `B`

In the repaired proof of Theorem 1, the upper layer of process `p` (on top of the implementation
`B`) runs a *copy* of the k-SA algorithm `A` with proposal `v`: it invokes `B.broadcast(m)`
whenever the copy wants to broadcast (with a fresh identifier) and records the copy's decisions.
The copy only sees its own invocations, returns and deliveries, and the deliveries of foreign
messages selected by a filter `F`. When `B` proposes to a k-SA object of a given set `R` while the
current copy has not decided yet, the copy is discarded and a fresh copy is started (`simStep`).

`prun par off` is the run of one process: rounds of four slots — a step of the upper layer, a
step of `B`, the immediate answer of the environment (a message sent to oneself is received; a
k-SA object answers `resp o w`), and the reception of one pending message (`pendNow` at once,
`pendLater` once the copy has decided).
-/

namespace Podc.NoBroadcastKSA.Camp

set_option linter.unusedSectionVars false

variable {P C V X O W : Type} [DecidableEq P]

/-- The full local events of a process: the events seen by `B`, and the internal steps of the
upper layer. -/
inductive FLEv (P M X O W : Type) where
  | b (e : CLEv P M X O W)
  | up

/-- The full local event produced by a step. -/
def CStep.floc {M : Type} : CStep P M X O W → FLEv P M X O W
  | .up _ => .up
  | s => match s.bloc with
    | some e => .b e
    | none => .up

/-- The full local history of `p` before time `t`. -/
def fhist {M : Type} (α : CExec P M X O W) (p : P) : ℕ → List (FLEv P M X O W)
  | 0 => []
  | t + 1 => fhist α p t ++
      ((α t).bind fun s => if s.proc = p then some s.floc else none).toList

/-- The part of a full local history seen by `B`. -/
def bview {M : Type} (h : List (FLEv P M X O W)) : List (CLEv P M X O W) :=
  h.filterMap fun e => match e with
    | .b e => some e
    | .up => none

lemma bview_append {M : Type} (h h' : List (FLEv P M X O W)) :
    bview (h ++ h') = bview h ++ bview h' := by
  simp [bview]

lemma CStep.bloc_floc {M : Type} (s : CStep P M X O W) :
    bview [s.floc] = s.bloc.toList := by
  rcases s with _ | _ | _ | _ | _ <;> simp [CStep.floc, CStep.bloc, bview]

lemma bhist_eq_bview {M : Type} (α : CExec P M X O W) (p : P) (t : ℕ) :
    bhist α p t = bview (fhist α p t) := by
  induction t with
  | zero => simp [bhist, fhist, bview]
  | succ t ih =>
    simp only [bhist, fhist, bview_append, ih]
    congr 1
    cases α t with
    | none => simp [bview]
    | some s =>
      simp only [Option.bind_some]
      split_ifs
      · exact (CStep.bloc_floc s).symm
      · simp [bview]

/-! ## The copy of `A` -/

section Copy

variable (A : Algo P C V) (p : P) (v : V) (R : Set O) (F : P → Msg C → Prop)

/-- Whether a local event of the copy is a decision. -/
def isDecL : LEv P (Msg C) V → Bool
  | .dec _ => true
  | _ => false

open Classical in
/-- One step of the simulation of the current copy of `A`: its view after a local event. -/
noncomputable def simStep (view : List (LEv P (Msg C) V)) :
    FLEv P (Msg C) X O W → List (LEv P (Msg C) V)
  | .b (.inv m) => view ++ [.bc m]
  | .b (.act (.ret m)) => if LEv.bc m ∈ view then view ++ [.ret m] else view
  | .b (.act (.deliver q m)) =>
      if (q = p ∧ LEv.bc m ∈ view) ∨ (q ≠ p ∧ F q m) then view ++ [.dl q m] else view
  | .b (.act (.propose o _)) => if o ∈ R ∧ view.any isDecL = false then [] else view
  | .up => match A.act p v view with
    | some (.decide w) => view ++ [.dec w]
    | _ => view
  | _ => view

/-- The view of the current copy after a full local history. -/
noncomputable def simView (h : List (FLEv P (Msg C) X O W)) : List (LEv P (Msg C) V) :=
  h.foldl (simStep A p v R F) []

lemma simView_append (h : List (FLEv P (Msg C) X O W)) (e : FLEv P (Msg C) X O W) :
    simView A p v R F (h ++ [e]) = simStep A p v R F (simView A p v R F h) e := by
  simp [simView, List.foldl_append]

end Copy

/-! ## The run of one process -/

/-- The parameters of the run of one process. -/
structure RunPar (P C V X O W : Type) where
  /-- the process -/
  p : P
  /-- the proposal of its copies of `A` -/
  v : V
  /-- proposing to an object of `R` while the copy has not decided discards the copy -/
  R : Set O
  /-- the foreign messages whose deliveries the copy sees -/
  F : P → Msg C → Prop
  /-- the answer of the k-SA object `o` to a proposal `w` -/
  resp : O → W → W
  /-- messages received at once, one per round (sender, message, sending time) -/
  pendNow : List (P × X × ℕ)
  /-- messages received once the copy has decided -/
  pendLater : List (P × X × ℕ)

/-- The local state of a process run. -/
structure LSt (P C X O W : Type) where
  /-- the full local history -/
  h : List (FLEv P (Msg C) X O W)
  /-- the last action of `B` -/
  last : Option (BAct P (Msg C) X O W)
  /-- number of messages of `pendNow` received -/
  iNow : ℕ
  /-- number of messages of `pendLater` received -/
  iLater : ℕ

/-- The initial local state. -/
def LSt.init : LSt P C X O W := ⟨[], none, 0, 0⟩

/-- Every invocation of the history is followed by its return. -/
def noPend {M : Type} [DecidableEq M] (h : List (FLEv P M X O W)) : Prop :=
  ∀ h₁ h₂ m, h = h₁ ++ FLEv.b (.inv m) :: h₂ → FLEv.b (.act (.ret m)) ∈ h₂

/-- Number of invocations in a history (the identifier of the next message). -/
def nInv {M : Type} (h : List (FLEv P M X O W)) : ℕ :=
  h.countP fun e => match e with
    | .b (.inv _) => true
    | _ => false

section Run

variable [DecidableEq C] (A : Algo P C V) (B : BAlgo P (Msg C) X O W)
  (par : RunPar P C V X O W)

open Classical in
/-- The step of the upper layer. -/
noncomputable def upperStep (h : List (FLEv P (Msg C) X O W)) : CStep P (Msg C) X O W :=
  match A.act par.p par.v (simView A par.p par.v par.R par.F h) with
  | some (.bcast c) => if noPend h then .inv par.p (nInv h, c) else .up par.p
  | _ => .up par.p

open Classical in
/-- One slot of the run: the step at global time `t`, local slot `j`, from local state `st`. -/
noncomputable def pstep (t j : ℕ) (st : LSt P C X O W) :
    Option (CStep P (Msg C) X O W) × LSt P C X O W :=
  if j % 4 = 0 then
    let s := upperStep A par st.h
    (some s, { st with h := st.h ++ [s.floc] })
  else if j % 4 = 1 then
    let a := B.next par.p (bview st.h)
    (some (.act par.p a), { st with h := st.h ++ [.b (.act a)], last := some a })
  else if j % 4 = 2 then
    match st.last with
    | some (.send q x) =>
      if q = par.p then
        (some (.recv par.p par.p x (t - 1)), { st with h := st.h ++ [.b (.recv par.p x)] })
      else (none, st)
    | some (.propose o w) =>
      (some (.dec par.p o (par.resp o w)), { st with h := st.h ++ [.b (.dec o (par.resp o w))] })
    | _ => (none, st)
  else
    match par.pendNow[st.iNow]? with
    | some (q, x, s) =>
      (some (.recv par.p q x s), { st with h := st.h ++ [.b (.recv q x)], iNow := st.iNow + 1 })
    | none =>
      if (simView A par.p par.v par.R par.F st.h).any isDecL then
        match par.pendLater[st.iLater]? with
        | some (q, x, s) =>
          (some (.recv par.p q x s),
            { st with h := st.h ++ [.b (.recv q x)], iLater := st.iLater + 1 })
        | none => (none, st)
      else (none, st)

/-- The local state after `j` slots (independent of the global times). -/
noncomputable def lst : ℕ → LSt P C X O W
  | 0 => LSt.init
  | j + 1 => (pstep A B par 0 j (lst j)).2

/-- The run of the process, started at global time `off`: its `j`-th slot. -/
noncomputable def prun (off j : ℕ) : Option (CStep P (Msg C) X O W) :=
  (pstep A B par (off + j) j (lst A B par j)).1

lemma pstep_snd (t t' j : ℕ) (st : LSt P C X O W) :
    (pstep A B par t j st).2 = (pstep A B par t' j st).2 := by
  obtain ⟨h, last, i1, i2⟩ := st
  unfold pstep
  split_ifs <;> try rfl
  all_goals rcases last with _ | (⟨q, x⟩ | ⟨o, w⟩ | _ | _ | _) <;> try rfl
  all_goals simp only
  all_goals split_ifs <;> rfl

lemma lst_succ (off j : ℕ) :
    lst A B par (j + 1) = (pstep A B par (off + j) j (lst A B par j)).2 := by
  rw [lst, pstep_snd]

end Run

end Podc.NoBroadcastKSA.Camp
