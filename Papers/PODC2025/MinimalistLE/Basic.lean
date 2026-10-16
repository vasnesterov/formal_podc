import Mathlib

/-!
# Algorithm BFW in the beeping model (Vacus–Ziccardi, PODC 2025, §1.1–§2)

Synchronous beeping model on a simple graph `G`: in every round each node either beeps or listens;
a listening node hears a beep iff at least one neighbour beeps. Algorithm BFW (Figure 1) has six
states: a phase `W` (waiting), `B` (beeping) or `F` (frozen), and a leader bit.

* `B → F`, `F → W` (frozen nodes ignore their environment), leader bit unchanged;
* `W` and a beep is heard → `B°` (a waiting leader that hears a beep is eliminated);
* `W•` and no beep heard → `B•` with probability `p`, else `W•`;
* `W°` and no beep heard → `W°`.

The only random transition is `W• → B•`. We make the execution a deterministic function of a
*coin field* `c : ℕ → V → Bool` (`c t v` = the coin of node `v` in round `t`, used only if `v` is in
`W•` and hears nothing). Every rule deciding when `W•` goes to `B•` (random or adversarial) is such a
coin field, so the results of §3 of the paper, which hold "independently of this rule", are stated for
all coin fields.
-/

namespace MinimalistLE

/-- The phase of a node: waiting, beeping or frozen. -/
inductive Phase
  | W
  | B
  | F
  deriving DecidableEq, Repr

/-- A state of BFW: a phase and a leader bit (`W•, B•, F•` have `leader = true`). -/
structure St where
  phase : Phase
  leader : Bool
  deriving DecidableEq, Repr

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Node `v` hears a beep in configuration `C`: some neighbour is beeping. -/
def Heard (C : V → St) (v : V) : Prop := ∃ w, G.Adj v w ∧ (C w).phase = .B

instance (C : V → St) (v : V) : Decidable (Heard G C v) := by
  unfold Heard; infer_instance

/-- One synchronous round of BFW (Figure 1); `coin v` decides `W• → B•`. -/
def next (C : V → St) (coin : V → Bool) (v : V) : St :=
  match (C v).phase with
  | .B => ⟨.F, (C v).leader⟩
  | .F => ⟨.W, (C v).leader⟩
  | .W =>
    if Heard G C v then ⟨.B, false⟩
    else if (C v).leader && coin v then ⟨.B, true⟩ else ⟨.W, (C v).leader⟩

/-- The execution of BFW from configuration `init` with coin field `c`. -/
def exec (init : V → St) (c : ℕ → V → Bool) : ℕ → V → St
  | 0 => init
  | t + 1 => next G (exec init c t) (c t)

/-- The paper's initial configuration: every node is a waiting leader `W•`. -/
def initAll : V → St := fun _ => ⟨.W, true⟩

/-- The assumption Eq. (2) of the paper: all nodes are waiting and there is a leader. -/
structure GoodInit (init : V → St) : Prop where
  waiting : ∀ v, (init v).phase = .W
  leader : ∃ v, (init v).leader = true

theorem goodInit_initAll [Nonempty V] : GoodInit (initAll (V := V)) :=
  ⟨fun _ => rfl, ⟨Classical.arbitrary V, rfl⟩⟩

/-- Number of beeps of `v` in rounds `0, …, t` (the paper's `N_t^beep(v)`). -/
def nbeep (init : V → St) (c : ℕ → V → Bool) (t : ℕ) (v : V) : ℕ :=
  ((Finset.range (t + 1)).filter (fun s => (exec G init c s v).phase = .B)).card

/-- Flow along an oriented edge `(u, v)` in configuration `C` (Definition 5). -/
def flow (C : V → St) (u v : V) : ℤ :=
  if (C u).phase = .B ∧ (C v).phase = .W then 1
  else if (C u).phase = .W ∧ (C v).phase = .B then -1 else 0

/-- Flow along a path (Definition 5): the sum of the flows of its oriented edges. -/
def walkFlow (C : V → St) : ∀ {u v : V}, G.Walk u v → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := w) _ p => flow C u w + walkFlow C p

/-! ### Elementary facts about one round -/

section step
variable {G}
variable {C : V → St} {coin : V → Bool} {v : V}

@[simp] theorem next_of_B (h : (C v).phase = .B) : next G C coin v = ⟨.F, (C v).leader⟩ := by
  simp [next, h]

@[simp] theorem next_of_F (h : (C v).phase = .F) : next G C coin v = ⟨.W, (C v).leader⟩ := by
  simp [next, h]

theorem next_of_W (h : (C v).phase = .W) : next G C coin v =
    if Heard G C v then ⟨.B, false⟩
    else if (C v).leader && coin v then ⟨.B, true⟩ else ⟨.W, (C v).leader⟩ := by
  simp [next, h]

end step

end MinimalistLE
