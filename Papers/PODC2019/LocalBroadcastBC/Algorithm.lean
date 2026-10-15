import Papers.PODC2019.LocalBroadcastBC.Model

/-!
# Algorithm 1 of [KNV19] as a lock-step protocol

Paths are lists of vertices (the paper's "paths" are sequences of pairwise adjacent nodes, i.e.
walks; `IsWalkList`). A message is a set of pairs `(b, Π)` (`Msg V`). Every node keeps

* `γ`: its binary state;
* `t`: the number of rounds so far;
* `acc K`: the value it has *received along* `K = Π - u` in the current phase (rule (iv)),
  where `u` is the neighbour from which `(b, Π)` was received;
* `fresh K`: the values received along `K` in the last round (to be forwarded now).

Every phase (one per `F` with `|F| ≤ f`, in the order of the list `phases f`) lasts `n` rounds of
flooding (step (a)); at the end of its last round a node performs steps (b) and (c) (`update`).
After all phases the node outputs `γ`.

Flooding rules (when `v` receives `(b, Π)` from `u`, `K = Π ++ [u]`):
(i) discard unless `K` is a walk of `G`; (ii) discard if `v` has already received a message
containing `Π` from `u` in this phase (i.e. `acc K ≠ none`); (iii) discard if `v ∈ Π` (equivalently
`v ∈ K`, since `u ≠ v`); (iv) otherwise accept and forward `(b, K)` in the next round. If a message
contains both `(0, Π)` and `(1, Π)`, the value `0` is taken (any deterministic choice works). A
neighbour that does not initiate flooding (no `(b, [])` in the first round of the phase) is treated
as having sent `(1, [])`.

Step (b) uses an arbitrary path selection `sel F u v` (a simple `uv`-path excluding `F`); the
correctness theorem holds for every such selection (`SelSpec`).
-/

open Finset

namespace LocalBroadcastBC

universe u

variable {V : Type u}

/-- Messages of Algorithm 1: sets of pairs `(value, path)`. -/
abbrev Msg (V : Type u) := Set (Bool × List V)

section Paths

variable (G : SimpleGraph V)

/-- A "path" in the sense of the paper: consecutive nodes are neighbours (a walk). -/
def IsWalkList (l : List V) : Prop := l.IsChain G.Adj

/-- A simple path. -/
def IsPathList (l : List V) : Prop := l.IsChain G.Adj ∧ l.Nodup

/-- The internal nodes of a path. -/
def internal (l : List V) : List V := l.tail.dropLast

end Paths

/-- The local state of a node. -/
structure LState (V : Type u) where
  γ : Bool
  t : ℕ
  acc : List V → Option Bool
  fresh : List V → Option Bool

/-- The phases: one for every `F` with `|F| ≤ f`. -/
noncomputable def phases [Fintype V] (f : ℕ) : List (Finset V) :=
  (univ.filter (fun F : Finset V => F.card ≤ f)).toList

lemma mem_phases [Fintype V] {f : ℕ} {F : Finset V} : F ∈ phases f ↔ F.card ≤ f := by
  simp [phases]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) (f : ℕ)
  (sel : Finset V → V → V → List V)

/-- Rounds per phase: `n`. -/
def rounds : ℕ := Fintype.card V

open Classical in
/-- The value read from a neighbour's message for the path `Π` in round `j` of a phase
(`none`: no such message). -/
noncomputable def readVal (j : ℕ) (path : List V) (m : Option (Msg V)) : Option Bool :=
  if (false, path) ∈ m.getD ∅ then some false
  else if (true, path) ∈ m.getD ∅ then some true
  else if j = 0 ∧ path = [] then some true
  else none

open Classical in
/-- The value newly received by `v` along `K` in round `j` of a phase (rules (i)–(iv)). -/
noncomputable def newVal (v : V) (j : ℕ) (acc : List V → Option Bool) (I : V → Option (Msg V))
    (K : List V) : Option Bool :=
  match K.getLast? with
  | none => none
  | some u =>
    if acc K = none ∧ G.Adj u v ∧ IsWalkList G K ∧ v ∉ K then readVal j K.dropLast (I u)
    else none

open Classical in
/-- `v` receives `δ` along `f + 1` node-disjoint `A v`-paths that exclude `F` (step (c)). -/
def Accepts (F A : Finset V) (v : V) (ac : List V → Option Bool) (δ : Bool) : Prop :=
  ∃ S : Finset (List V), S.card = f + 1 ∧
    (∀ P ∈ S, IsWalkList G P ∧ (∃ a ∈ A, P.head? = some a) ∧ P.getLast? = some v ∧
      (∀ x ∈ internal P, x ∉ F) ∧ ac P.dropLast = some δ) ∧
    ∀ P ∈ S, ∀ P' ∈ S, P ≠ P' → ∀ x ∈ P, x ∈ P' → x = v

open Classical in
/-- The value `v` received from `u` along the selected path `P_uv` (step (b)); `v` receives its own
state along `P_vv`. -/
noncomputable def recv (F : Finset V) (v : V) (γ : Bool) (ac : List V → Option Bool) (u : V) :
    Option Bool :=
  if u = v then some γ else ac (sel F u v).dropLast

open Classical in
/-- `Z_v`. -/
noncomputable def Zset (F : Finset V) (v : V) (γ : Bool) (ac : List V → Option Bool) : Finset V :=
  univ.filter (fun u => recv sel F v γ ac u = some false)

omit [Fintype V] in
lemma mem_Zset [Fintype V] {F : Finset V} {v : V} {γ : Bool} {ac : List V → Option Bool} {u : V} :
    u ∈ Zset sel F v γ ac ↔ recv sel F v γ ac u = some false := by
  unfold Zset; simp

/-- The case distinction of step (c): returns `(A_v, B_v)` from `Z_v`. -/
def sets (F Z : Finset V) : Finset V × Finset V :=
  if (Z ∩ F).card ≤ f / 2 then
    (if f < (univ \ Z).card then (univ \ Z, Z) else (Z, univ \ Z))
  else
    (if f < Z.card then (Z, univ \ Z) else (univ \ Z, Z))

open Classical in
/-- Steps (b) and (c) of a phase with set `F`, for node `v` with state `γ` that received `ac`. -/
noncomputable def update (F : Finset V) (v : V) (γ : Bool) (ac : List V → Option Bool) : Bool :=
  let AB := sets f F (Zset sel F v γ ac)
  if v ∈ AB.2 then
    (if Accepts G f F AB.1 v ac false then false
     else if Accepts G f F AB.1 v ac true then true else γ)
  else γ

/-- The update at the end of phase `k`. -/
noncomputable def phaseUpdate (k : ℕ) (v : V) (γ : Bool) (ac : List V → Option Bool) : Bool :=
  match (phases (V := V) f)[k]? with
  | none => γ
  | some F => update G f sel F v γ ac

/-- One round of a node: process the inbox, and at the end of a phase run steps (b), (c). -/
noncomputable def stepState (v : V) (st : LState V) (I : V → Option (Msg V)) : LState V :=
  let j := st.t % rounds (V := V)
  let fr := newVal G v j st.acc I
  let ac := fun K => (st.acc K).or (fr K)
  if j + 1 = rounds (V := V) then
    { γ := phaseUpdate G f sel (st.t / rounds (V := V)) v st.γ ac, t := st.t + 1,
      acc := fun _ => none, fresh := fun _ => none }
  else { γ := st.γ, t := st.t + 1, acc := ac, fresh := fr }

/-- The initial state. -/
def initState (x : Bool) : LState V := ⟨x, 0, fun _ => none, fun _ => none⟩

/-- The local state of `v` after a history. -/
noncomputable def state (v : V) (x : Bool) (h : Cslib.Byzantine.LockStep.History V (Msg V)) :
    LState V :=
  h.foldl (stepState G f sel v) (initState x)

/-- The message sent by a node in state `st`: `(γ, ⊥)` in the first round of a phase, otherwise
the values received in the previous round. -/
def outMsg (st : LState V) : Msg V :=
  if st.t % rounds (V := V) = 0 then {(st.γ, [])} else {p | st.fresh p.2 = some p.1}

/-- **Algorithm 1** of [KNV19] as a lock-step protocol. -/
noncomputable def alg1 : Cslib.Byzantine.LockStep.Protocol V Bool (Msg V) Bool where
  send v x h _ := some (outMsg (state G f sel v x h))
  decide v x h :=
    if (phases (V := V) f).length * rounds (V := V) ≤ h.length then
      some (state G f sel v x h).γ
    else none

lemma alg1_isBroadcast : IsBroadcast (alg1 G f sel) := fun _ _ _ _ _ => rfl

/-- Specification of the path selection of step (b): `sel F u v` is a simple `uv`-path excluding
`F`. -/
def SelSpec : Prop :=
  ∀ F : Finset V, F.card ≤ f → ∀ u v, u ≠ v →
    IsPathList G (sel F u v) ∧ (sel F u v).head? = some u ∧ (sel F u v).getLast? = some v ∧
      ∀ x ∈ internal (sel F u v), x ∉ F

end LocalBroadcastBC
