import Mathlib

/-!
# The bounded communication model without clocks (`bcm`) — Section 2

Dan, Manohar, Moses, *On Using Time Without Clocks via Zigzag Causality*, PODC 2017
(arXiv 1705.08627v1).

* `Net` — a network `(Procs, Chans)` with lower/upper delivery bounds `1 ≤ L i j ≤ U i j`.
* `LState` — a local state: an initial state followed by the list of *batches* the process has
  received (one batch per activation: the internal messages `(sender, content)` and the external
  messages delivered at that time). Processes have no clocks: time is not recorded.
* `Sys` — a context `γ = ((Net, L, U), G₀)` together with a deterministic protocol
  `send i ℓ j : Option M` (the message process `i` in local state `ℓ` sends to `j`; it is sent when
  `i` is activated in state `ℓ`).
* `Sched` — the environment's choices: initial states, delivery times and external deliveries.
  The local states of the run are *computed* from a schedule (`Sys.st`); a run of the system
  `R(P, γ)` is a schedule satisfying `Sys.Valid` (initial state in `G₀`, every message delivered
  within `[L, U]`, every external message delivered at most once).
* Basic nodes `σ = (i, ℓ)`, `appears`, `timer`, `recv` (where the message sent at a node is
  delivered), general nodes `⟨σ, p⟩` (`GNode`, `basic`), Lamport's happens-before `HB`,
  timed precedence `Prec`, `supports` and knowledge `Knows`.
* Full-information protocols `IsFIP` and flooding full-information protocols `IsFFIP`.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

/-- A time-bounded network: channels and lower/upper bounds on message transmission times,
`1 ≤ L i j ≤ U i j` on every channel. -/
structure Net (P : Type*) where
  /-- `Chan i j`: there is a channel from `i` to `j`. -/
  Chan : P → P → Prop
  /-- Lower bounds on transmission times. -/
  L : P → P → ℕ
  /-- Upper bounds on transmission times. -/
  U : P → P → ℕ
  one_le_L : ∀ i j, Chan i j → 1 ≤ L i j
  L_le_U : ∀ i j, Chan i j → L i j ≤ U i j

/-- What a process observes in one activation: the internal messages `(sender, content)` and the
external messages delivered to it at that time. -/
structure Batch (P M E : Type*) where
  msgs : Finset (P × M)
  ext : Finset E

/-- A local state: an initial state followed by the sequence of batches received so far. -/
structure LState (P S M E : Type*) where
  init : S
  hist : List (Batch P M E)

variable {P S M E : Type*}

/-- One time step of a process: if nothing is delivered the local state does not change (the
process cannot observe the passage of time); otherwise the batch is appended. -/
noncomputable def LState.step (ℓ : LState P S M E) (b : Batch P M E) : LState P S M E :=
  if b.msgs = ∅ ∧ b.ext = ∅ then ℓ else ⟨ℓ.init, ℓ.hist ++ [b]⟩

/-- A context together with a deterministic protocol. -/
structure Sys (P S M E : Type*) where
  /-- The time-bounded network. -/
  net : Net P
  /-- `send i ℓ j`: the message that `i`, activated in local state `ℓ`, sends to `j` (if any).
  Messages are sent only along channels. -/
  send : P → LState P S M E → P → Option M
  /-- The possible initial global states `G₀`. -/
  G0 : Set (P → S)

/-- The environment's (nondeterministic) choices in a run: initial states, the delivery time
`dlv i s j` of the message sent by `i` at time `s` to `j`, and the external messages delivered to
`j` at time `t`. -/
structure Sched (P S E : Type*) where
  g : P → S
  dlv : P → ℕ → P → ℕ
  ext : ℕ → P → Finset E

/-- A basic node `(i, ℓ)`: a process and a local state of it. -/
abbrev BNode (P S M E : Type*) := P × LState P S M E

/-- `i` is activated at time `s` in the history `h` (its local state changes). -/
def ActiveH (h : ℕ → P → LState P S M E) (i : P) (s : ℕ) : Prop := 0 < s ∧ h s i ≠ h (s - 1) i

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E)

/-! ### Computing the local states of a run -/

/-- The internal messages delivered to `j` at time `t + 1`, given the history `h` up to time `t`. -/
def msgSet (h : ℕ → P → LState P S M E) (t : ℕ) (j : P) : Set (P × M) :=
  {x | ∃ s < t + 1, ActiveH h x.1 s ∧ γ.net.Chan x.1 j ∧ r.dlv x.1 s j = t + 1 ∧
    γ.send x.1 (h s x.1) j = some x.2}

theorem msgSet_finite [Finite P] (h : ℕ → P → LState P S M E) (t : ℕ) (j : P) :
    (γ.msgSet r h t j).Finite := by
  have hfin : (Set.univ ×ˢ Set.Iio (t + 1) : Set (P × ℕ)).Finite :=
    Set.finite_univ.prod (Set.finite_Iio _)
  refine (hfin.biUnion (t := fun p => {x : P × M | x.1 = p.1 ∧ γ.send p.1 (h p.2 p.1) j = some x.2})
    fun p _ => ?_).subset ?_
  · refine Set.Subsingleton.finite ?_
    rintro ⟨a, m⟩ ⟨ha, hm⟩ ⟨b, m'⟩ ⟨hb, hm'⟩
    simp only at ha hb hm hm'
    subst ha hb
    rw [hm] at hm'
    cases hm'
    rfl
  · rintro ⟨i, m⟩ ⟨s, hs, -, -, -, hm⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, Set.mem_Iio,
      true_and, exists_prop, Prod.exists]
    exact ⟨i, s, hs, rfl, hm⟩

variable [Finite P]

/-- The batch delivered to `j` at time `t + 1`, given the history `h` up to time `t`. -/
noncomputable def batchH (h : ℕ → P → LState P S M E) (t : ℕ) (j : P) : Batch P M E :=
  ⟨(γ.msgSet_finite r h t j).toFinset, r.ext (t + 1) j⟩

/-- `histAux t` is the history of the run up to time `t` (later times are arbitrary). -/
noncomputable def histAux : ℕ → ℕ → P → LState P S M E
  | 0 => fun _ i => ⟨r.g i, []⟩
  | t + 1 => fun s =>
      if s ≤ t then histAux t s else fun j => (histAux t t j).step (γ.batchH r (histAux t) t j)

/-- The local state `r_i(t)` of process `i` at time `t` in the run given by schedule `r`. -/
noncomputable def st (t : ℕ) (i : P) : LState P S M E := γ.histAux r t t i

theorem histAux_of_le {s t : ℕ} (h : s ≤ t) : γ.histAux r t s = γ.st r s := by
  induction t with
  | zero => obtain rfl : s = 0 := by omega
            rfl
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hs | hs
    · have : s ≤ t := by omega
      simp only [histAux, this, ite_true]
      exact ih this
    · obtain rfl : s = t + 1 := by omega
      rfl

/-- `i` is activated at time `s` (its local state changes at `s`). -/
def Active (i : P) (s : ℕ) : Prop := ActiveH (γ.st r) i s

/-- The batch delivered to `j` at time `t + 1`. -/
noncomputable def batch (t : ℕ) (j : P) : Batch P M E := γ.batchH r (γ.st r) t j

theorem batchH_congr {h h' : ℕ → P → LState P S M E} {t : ℕ} (hh : ∀ s ≤ t, h s = h' s) (j : P) :
    γ.batchH r h t j = γ.batchH r h' t j := by
  have : γ.msgSet r h t j = γ.msgSet r h' t j := by
    ext ⟨i, m⟩
    simp only [msgSet, ActiveH, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨s, hs, ⟨h0, ha⟩, hc, hd, hm⟩
      refine ⟨s, hs, ⟨h0, ?_⟩, hc, hd, ?_⟩
      · rwa [← hh s (by omega), ← hh (s - 1) (by omega)]
      · rwa [← hh s (by omega)]
    · rintro ⟨s, hs, ⟨h0, ha⟩, hc, hd, hm⟩
      refine ⟨s, hs, ⟨h0, ?_⟩, hc, hd, ?_⟩
      · rwa [hh s (by omega), hh (s - 1) (by omega)]
      · rwa [hh s (by omega)]
  simp only [batchH, this]

theorem st_zero (i : P) : γ.st r 0 i = ⟨r.g i, []⟩ := rfl

/-- The local states of a run evolve by `LState.step` with the delivered batches. -/
theorem st_succ (t : ℕ) (j : P) : γ.st r (t + 1) j = (γ.st r t j).step (γ.batch r t j) := by
  show γ.histAux r (t + 1) (t + 1) j = _
  simp only [histAux, show ¬ (t + 1 ≤ t) by omega, ite_false]
  rw [batch, γ.batchH_congr r (h' := γ.st r) (fun s hs => γ.histAux_of_le r hs)]
  rfl

theorem mem_batch_msgs {t : ℕ} {j i : P} {m : M} :
    (i, m) ∈ (γ.batch r t j).msgs ↔ ∃ s < t + 1, γ.Active r i s ∧ γ.net.Chan i j ∧
      r.dlv i s j = t + 1 ∧ γ.send i (γ.st r s i) j = some m := by
  simp [batch, batchH, msgSet, Active]

theorem batch_ext (t : ℕ) (j : P) : (γ.batch r t j).ext = r.ext (t + 1) j := rfl

/-! ### Runs -/

/-- `i` sends a message to `j` at time `s`: it is activated at `s`, there is a channel, and the
protocol sends. -/
def Sends (i : P) (s : ℕ) (j : P) : Prop :=
  γ.Active r i s ∧ γ.net.Chan i j ∧ (γ.send i (γ.st r s i) j).isSome

/-- A schedule is a run of the system `R(P, γ)`: the initial global state is in `G₀`, every sent
message is delivered within its bounds, and every external message is delivered at most once. -/
structure Valid : Prop where
  init : r.g ∈ γ.G0
  bounds : ∀ i s j, γ.Sends r i s j →
    s + γ.net.L i j ≤ r.dlv i s j ∧ r.dlv i s j ≤ s + γ.net.U i j
  ext_unique : ∀ e t j t' j', e ∈ r.ext t j → e ∈ r.ext t' j' → t = t' ∧ j = j'

/-! ### Basic nodes, `timer`, messages -/

/-- The basic node `σ` appears in the run. -/
def appears (σ : BNode P S M E) : Prop := ∃ t, γ.st r t σ.1 = σ.2

/-- `timer_r(σ)`: the first time at which the basic node `σ` appears (`0` if it does not). -/
noncomputable def timer (σ : BNode P S M E) : ℕ :=
  if h : γ.appears r σ then Nat.find h else 0

/-- `recv r σ j`: the basic node at which the message sent at `σ` to `j` is delivered (`none` if
`σ` does not send to `j`). A node sends at the time it is created. -/
noncomputable def recv (σ : BNode P S M E) (j : P) : Option (BNode P S M E) :=
  if γ.Sends r σ.1 (γ.timer r σ) j then some (j, γ.st r (r.dlv σ.1 (γ.timer r σ) j) j) else none

/-! ### General nodes -/

end Sys

/-- A general node `⟨σ, p⟩`: the node reached by the message chain that leaves the basic node `σ`
and follows the path `σ.1 :: path` in the network (`path = []` denotes `σ` itself). -/
structure GNode (P S M E : Type*) where
  root : BNode P S M E
  path : List P

/-- The last process of a nonempty list `i :: q`. -/
def lastP (i : P) (q : List P) : P := (i :: q).getLast (List.cons_ne_nil _ _)

/-- The process of a general node (the last process of its path). -/
def GNode.proc (θ : GNode P S M E) : P := lastP θ.root.1 θ.path

/-- `θ · q`: extend the message chain of `θ` along `q`. -/
def GNode.ext (θ : GNode P S M E) (q : List P) : GNode P S M E := ⟨θ.root, θ.path ++ q⟩

/-- The general node denoting the basic node `σ` itself. -/
def GNode.ofB (σ : BNode P S M E) : GNode P S M E := ⟨σ, []⟩

/-- Sum of the lower bounds along the path `i :: q`. -/
def Net.Lp (N : Net P) : P → List P → ℕ
  | _, [] => 0
  | i, j :: q => N.L i j + N.Lp j q

/-- Sum of the upper bounds along the path `i :: q`. -/
def Net.Up (N : Net P) : P → List P → ℕ
  | _, [] => 0
  | i, j :: q => N.U i j + N.Up j q

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E) [Finite P]

/-- The basic node at the end of the message chain from `σ` along `q`, if it exists. -/
noncomputable def gbasic : BNode P S M E → List P → Option (BNode P S M E)
  | σ, [] => if γ.appears r σ then some σ else none
  | σ, j :: q => (γ.recv r σ j).bind fun σ' => gbasic σ' q

/-- `basic(θ, r)`: the basic node that corresponds to the general node `θ` in `r`. -/
noncomputable def basic (θ : GNode P S M E) : Option (BNode P S M E) := γ.gbasic r θ.root θ.path

/-- The general node `θ` appears in `r`. -/
def appearsG (θ : GNode P S M E) : Prop := (γ.basic r θ).isSome

/-- `timer_r(θ) = timer_r(basic(θ, r))`. -/
noncomputable def timerG (θ : GNode P S M E) : ℕ :=
  match γ.basic r θ with
  | some σ => γ.timer r σ
  | none => 0

/-- One step of Lamport's happens-before relation: locality (same process, not later), or a
message. -/
def HBStep (σ σ' : BNode P S M E) : Prop :=
  (γ.appears r σ ∧ γ.appears r σ' ∧ σ.1 = σ'.1 ∧ γ.timer r σ ≤ γ.timer r σ') ∨
    ∃ j, γ.recv r σ j = some σ'

/-- Lamport's happens-before relation `σ ⇝_r σ'` on basic nodes (Definition 2): the transitive
closure of locality and message delivery. -/
def HB (σ σ' : BNode P S M E) : Prop := Relation.TransGen (γ.HBStep r) σ σ'

/-- Timed precedence `(R, r) ⊨ θ₁ --x--> θ₂`: both nodes appear in `r` and
`timer_r(θ₁) + x ≤ timer_r(θ₂)`. -/
def Prec (θ₁ : GNode P S M E) (x : ℤ) (θ₂ : GNode P S M E) : Prop :=
  ∃ σ₁ σ₂, γ.basic r θ₁ = some σ₁ ∧ γ.basic r θ₂ = some σ₂ ∧
    (γ.timer r σ₁ : ℤ) + x ≤ γ.timer r σ₂

/-- The system `R(P, γ)` *supports* `θ₁ --x--> θ₂`: in every run in which one of the nodes
appears, both appear and the precedence holds. -/
def Supports (θ₁ : GNode P S M E) (x : ℤ) (θ₂ : GNode P S M E) : Prop :=
  ∀ r : Sched P S E, γ.Valid r → (γ.appearsG r θ₁ ∨ γ.appearsG r θ₂) → γ.Prec r θ₁ x θ₂

/-- Knowledge at a basic node: `(R, r) ⊨ K_σ φ` iff `φ` holds in every run of `R(P, γ)` in which
`σ` appears (`r ∼_σ r'`). The run `r` itself only matters through the requirement that `σ`
appears in it. -/
def Knows (σ : BNode P S M E) (φ : Sched P S E → Prop) : Prop :=
  ∀ r' : Sched P S E, γ.Valid r' → γ.appears r' σ → φ r'

/-- A full-information protocol: the content of a message determines the sender's local state. -/
def IsFIP : Prop :=
  ∀ i j j' ℓ ℓ' m, γ.send i ℓ j = some m → γ.send i ℓ' j' = some m → ℓ = ℓ'

/-- A flooding full-information protocol (FFIP): full information, and every activated process
sends a message to all its out-neighbours. -/
def IsFFIP : Prop := γ.IsFIP ∧ ∀ i ℓ j, γ.net.Chan i j → (γ.send i ℓ j).isSome

end Sys

end Podc.ZigzagCausality
