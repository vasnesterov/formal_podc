import Mathlib
import Cslib.Computability.Distributed.Knowledge.Basic

/-!
# The model of Alpturer–Halpern–van der Meyden (PODC 2023), §§2–6

*Optimal Eventual Byzantine Agreement Protocols with Omission Failures.*

* **Information-exchange protocols** (§3). The local state of agent `i` is a pair `(core, x)`:
  `core = ⟨time, init, decided, jd⟩` is the part every EBA context must have (§5), `x : γ.X` is the
  rest. Messages are `Option γ.M` (`none` = `⊥`). `γ.tag : γ.M → Option Val` splits messages into
  `M⁰` (`tag = some 0`), `M¹` (`tag = some 1`) and `M²` (`tag = none`); deciding `v` sends an
  `Mᵛ`-message to everybody, `noop` sends `⊥` or `M²`-messages. The core part of the state is updated
  exactly as required by the definition of EBA contexts; the extra part by an arbitrary `γ.δX`.
* **Failure patterns** `(N, F)`, `F m i j` = "the message from `i` to `j` in round `m + 1` is
  delivered"; a failure model is a set of patterns; `SO n t` is sending omissions with `≤ t`
  faulty agents.
* **Runs.** A run is determined by its initial global state (`Config`: failure pattern, initial
  preferences, initial extra state) and the action protocol (`state P c m i` = `r_i(m)`).
* **Knowledge** (`Knows P i s φ`): `φ` holds at every point of the system `I_{γ,P}` where `i` has
  local state `s` (the paper's `I, s ⊨ K_i φ`).
* The knowledge-based program **`P0`**, **implementation**, the **EBA specification**,
  **domination** and **optimality** (§5), **0-chains** and **safety** (§6).

Values `0, 1` are `Fin 2`; `1 - v` is the other value.
-/

namespace Podc.OptimalEBAOmission

open Classical

/-- Binary values (initial preferences and decisions). -/
abbrev Val := Fin 2

/-- Actions: `decide v` or `noop`. -/
inductive Act where
  | decide (v : Val)
  | noop
  deriving DecidableEq

/-- The components every local state of an EBA context has: `⟨time, init, decided, jd⟩`
(`decided = none` is `⊥`; `jd = some v`: the agent learned that some agent just decided `v`). -/
@[ext] structure Core where
  /-- `time_i`. -/
  time : ℕ
  /-- `init_i`. -/
  init : Val
  /-- `decided_i ∈ {0, 1, ⊥}`. -/
  decided : Option Val
  /-- `jd_i ∈ {0, 1, ⊥}`. -/
  jd : Option Val
  deriving DecidableEq

/-- A failure pattern `(N, F)`: `N` is the set of nonfaulty agents and `F m i j` says whether the
message from `i` to `j` in round `m + 1` is delivered. -/
structure Pattern (n : ℕ) where
  /-- The nonfaulty agents. -/
  N : Finset (Fin n)
  /-- Delivery: `F m i j` for the message from `i` to `j` in round `m + 1`. -/
  F : ℕ → Fin n → Fin n → Bool

/-- The sending-omissions failure model `SO(t)`: at most `t` faulty agents, and only faulty agents
omit messages. -/
def SO (n t : ℕ) : Set (Pattern n) :=
  {α | (Finset.univ \ α.N).card ≤ t ∧ ∀ m i j, α.F m i j = false → i ∉ α.N}

/-- An **EBA context** for `n` agents (§5): an information-exchange protocol satisfying the EBA
constraints, together with a failure model. (The interpretation `π` of the paper is not needed:
formulas are semantic predicates.) -/
structure Context (n : ℕ) where
  /-- The non-EBA part of the local states. -/
  X : Type
  /-- Messages (`none : Option M` is `⊥`). -/
  M : Type
  /-- `tag m = some v` iff `m ∈ Mᵛ` (`v ∈ {0,1}`); `tag m = none` iff `m ∈ M²`. -/
  tag : M → Option Val
  /-- Initial values of the non-EBA part, for agent `i` with initial preference `v`. -/
  initX : Fin n → Val → Set X
  /-- Every agent can start with either preference ("independently selected value init_i"). -/
  initX_nonempty : ∀ i v, (initX i v).Nonempty
  /-- Message selection `μ_i(s, a)(j)`. -/
  μ : Fin n → Core × X → Act → Fin n → Option M
  /-- Deciding `v` sends an `Mᵛ`-message to every agent. -/
  μ_decide : ∀ i s v j, ∃ m, μ i s (.decide v) j = some m ∧ tag m = some v
  /-- Not deciding sends `⊥` or an `M²`-message. -/
  μ_noop : ∀ i s j m, μ i s .noop j = some m → tag m = none
  /-- Update of the non-EBA part of the state. -/
  δX : Fin n → Core × X → Act → (Fin n → Option M) → X
  /-- The failure model. -/
  FM : Set (Pattern n)

namespace Context

variable {n : ℕ} (γ : Context n)

/-- Local states. -/
abbrev L := Core × γ.X

/-- Action protocols `P_i : L_i → A_i`. -/
abbrev Protocol := Fin n → γ.L → Act

/-- The new value of `decided` after action `a`. -/
def newDec (d : Option Val) : Act → Option Val
  | .decide v => some v
  | .noop => d

/-- The new value of `jd`: `0` if a message from an agent deciding `0` was received, else `1` if a
message from an agent deciding `1` was received, else `⊥`. (The paper does not say what happens
if both are received; this never happens with implementations of `P0`.) -/
noncomputable def jdOf (rcv : Fin n → Option γ.M) : Option Val :=
  if ∃ j m, rcv j = some m ∧ γ.tag m = some 0 then some 0
  else if ∃ j m, rcv j = some m ∧ γ.tag m = some 1 then some 1 else none

/-- The state update `δ_i`: time increases by one, `init` is kept, `decided` records a decision,
`jd` records what was just decided; the rest is updated by `δX`. -/
noncomputable def δ (i : Fin n) (s : γ.L) (a : Act) (rcv : Fin n → Option γ.M) : γ.L :=
  (⟨s.1.time + 1, s.1.init, newDec s.1.decided a, γ.jdOf rcv⟩, γ.δX i s a rcv)

/-- The initial global state of a run: a failure pattern, initial preferences and the initial
values of the non-EBA parts of the local states. -/
structure Config where
  /-- The failure pattern (state of the environment). -/
  pat : Pattern n
  /-- Initial preferences. -/
  init : Fin n → Val
  /-- Initial extra state. -/
  x0 : Fin n → γ.X

variable {γ}

/-- A configuration is admissible if its pattern is in the failure model and the initial local
states are initial states of the information-exchange protocol. -/
def Config.Valid (c : γ.Config) : Prop := c.pat ∈ γ.FM ∧ ∀ i, c.x0 i ∈ γ.initX i (c.init i)

variable (γ)

/-- The run of protocol `P` from configuration `c`: `state P c m i = r_i(m)`. -/
noncomputable def state (P : γ.Protocol) (c : γ.Config) : ℕ → Fin n → γ.L
  | 0 => fun i => (⟨0, c.init i, none, none⟩, c.x0 i)
  | k + 1 => fun i =>
      γ.δ i (state P c k i) (P i (state P c k i))
        (fun j => if c.pat.F k j i then γ.μ j (state P c k j) (P j (state P c k j)) i else none)

variable {γ}

/-- `decided_j` at time `m` of the run of `P` from `c`. -/
noncomputable abbrev dec (P : γ.Protocol) (c : γ.Config) (m : ℕ) (j : Fin n) : Option Val :=
  (γ.state P c m j).1.decided

/-- `deciding_j = v` at `(c, m)`: `decided_j = ⊥ ∧ ◯ decided_j = v` ("`j` decides `v` in round
`m + 1`"). -/
def Deciding (P : γ.Protocol) (c : γ.Config) (m : ℕ) (j : Fin n) (v : Val) : Prop :=
  dec P c m j = none ∧ dec P c (m + 1) j = some v

/-- `jdecided_j = v` at `(c, m)`: `decided_j = v ∧ ⊖ decided_j = ⊥` (`j` just decided `v`). -/
def JDecided (P : γ.Protocol) (c : γ.Config) (m : ℕ) (j : Fin n) (v : Val) : Prop :=
  0 < m ∧ dec P c m j = some v ∧ dec P c (m - 1) j = none

/-- `I_{γ,P}, s ⊨ K_i φ`: `φ` holds at every point of the system of `P` where `i` has local state
`s`. -/
def Knows (P : γ.Protocol) (i : Fin n) (s : γ.L) (φ : γ.Config → ℕ → Prop) : Prop :=
  ∀ c : γ.Config, c.Valid → ∀ m, γ.state P c m i = s → φ c m

/-- The knowledge-based program `P0` (§6), with its tests interpreted in the system of `P`:
```
if decided_i ≠ ⊥ then noop
else if init_i = 0 ∨ K_i (⋁_j jdecided_j = 0) then decide_i(0)
else if K_i (⋀_j ¬(deciding_j = 0)) then decide_i(1)
else noop
``` -/
noncomputable def P0 (P : γ.Protocol) : γ.Protocol := fun i s =>
  if s.1.decided ≠ none then .noop
  else if s.1.init = 0 ∨ Knows P i s (fun c m => ∃ j, JDecided P c m j 0) then .decide 0
  else if Knows P i s (fun c m => ∀ j, ¬ Deciding P c m j 0) then .decide 1
  else .noop

/-- `P` implements the knowledge-based program `P0` in `γ`: `P_i(s) = P0_i^{I_{γ,P}}(s)` for all
local states `s` that arise in the system of `P`. -/
def Implements (P : γ.Protocol) : Prop :=
  ∀ c : γ.Config, c.Valid → ∀ m i, P i (γ.state P c m i) = P0 P i (γ.state P c m i)

/-- `P` is an **EBA decision protocol** for `γ` (§5): Unique Decision, Agreement, Validity and
Termination are valid in `I_{γ,P}`. -/
structure IsEBA (P : γ.Protocol) : Prop where
  /-- `decided_i = v ⇒ □ ¬(decided_i = 1 - v)`. -/
  unique : ∀ c : γ.Config, c.Valid → ∀ i m v, dec P c m i = some v →
    ∀ m' ≥ m, dec P c m' i ≠ some (1 - v)
  /-- `¬(i ∈ N ∧ j ∈ N ∧ decided_i = v ∧ decided_j = v')` for `v ≠ v'`. -/
  agreement : ∀ c : γ.Config, c.Valid → ∀ i ∈ c.pat.N, ∀ j ∈ c.pat.N, ∀ m v v',
    dec P c m i = some v → dec P c m j = some v' → v = v'
  /-- `(decided_i = v ∧ i ∈ N) ⇒ ∃v`. -/
  validity : ∀ c : γ.Config, c.Valid → ∀ i ∈ c.pat.N, ∀ m v,
    dec P c m i = some v → ∃ j, c.init j = v
  /-- `i ∈ N ⇒ ◇ (decided_i ≠ ⊥)`. -/
  termination : ∀ c : γ.Config, c.Valid → ∀ i ∈ c.pat.N, ∀ m, ∃ m' ≥ m, dec P c m' i ≠ none

/-- `Dominates P P'` is the paper's `P' ≤_γ P` ("`P` dominates `P'`"): in corresponding runs, if
a nonfaulty `i` performs `decide_i(v)` at time `m` with `P`, then `P'` does not perform any
`decide_i(w)` at a time `m' < m`. -/
def Dominates (P P' : γ.Protocol) : Prop :=
  ∀ c : γ.Config, c.Valid → ∀ i ∈ c.pat.N, ∀ m v, P i (γ.state P c m i) = .decide v →
    ∀ m' < m, ∀ w, P' i (γ.state P' c m' i) ≠ .decide w

/-- `P` strictly dominates `P'`: `P' ≤_γ P` and not `P ≤_γ P'`. -/
def StrictlyDominates (P P' : γ.Protocol) : Prop := Dominates P P' ∧ ¬ Dominates P' P

/-- `P` is **optimal** for `γ`: an EBA decision protocol not strictly dominated by any EBA decision
protocol. -/
def Optimal (P : γ.Protocol) : Prop :=
  IsEBA P ∧ ∀ P', IsEBA P' → ¬ StrictlyDominates P' P

/-- A protocol that performs no action once it has decided (the decision is a one-shot action).
The proof of Theorem 6.3 tacitly assumes that competitors are of this form. -/
def OneShot (P : γ.Protocol) : Prop := ∀ i (s : γ.L), s.1.decided ≠ none → P i s = .noop

/-- Optimality among one-shot competitors. -/
def OptimalOneShot (P : γ.Protocol) : Prop :=
  IsEBA P ∧ ∀ P', IsEBA P' → OneShot P' → ¬ StrictlyDominates P' P

/-- **0-chain, as defined in the paper** (§6): distinct agents `a 0, …, a m` with
(a) `init_{a 0} = 0`, (b) `a k` first decides `0` in round `k + 1`, and (c) for `1 ≤ k ≤ m`, `a k`
knows at `(c, k)` that `a (k - 1)` has just decided `0`. -/
def IsZeroChainLit (P : γ.Protocol) (c : γ.Config) (m : ℕ) (a : ℕ → Fin n) : Prop :=
  (∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l) ∧ c.init (a 0) = 0 ∧
  (∀ k ≤ m, Deciding P c k (a k) 0) ∧
  ∀ k, 1 ≤ k → k ≤ m → Knows P (a k) (γ.state P c k (a k)) (fun c' m' => JDecided P c' m' (a (k - 1)) 0)

/-- **0-chain, repaired**: as `IsZeroChainLit`, but in (c) `a k` only needs to know that *some*
agent has just decided `0` (by (b), `a (k - 1)` has). This is the notion the paper's proofs use
(Prop. 6.1: "`K_i(⋁_j jdecided_j = 0)` … so `K_i(jdecided_j = 0)` for some `j`"). -/
def IsZeroChain (P : γ.Protocol) (c : γ.Config) (m : ℕ) (a : ℕ → Fin n) : Prop :=
  (∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l) ∧ c.init (a 0) = 0 ∧
  (∀ k ≤ m, Deciding P c k (a k) 0) ∧
  ∀ k, 1 ≤ k → k ≤ m → Knows P (a k) (γ.state P c k (a k)) (fun c' m' => ∃ j, JDecided P c' m' j 0)

/-- `i` has received a 0-chain by `(c, m)` (paper's definition). -/
def ReceivedChainLit (P : γ.Protocol) (c : γ.Config) (m : ℕ) (i : Fin n) : Prop :=
  ∃ m' ≤ m, ∃ a, IsZeroChainLit P c m' a ∧ a m' = i

/-- `i` has received a (repaired) 0-chain by `(c, m)`. -/
def ReceivedChain (P : γ.Protocol) (c : γ.Config) (m : ℕ) (i : Fin n) : Prop :=
  ∃ m' ≤ m, ∃ a, IsZeroChain P c m' a ∧ a m' = i

/-- The two **safety** conditions of Definition 6.2 for the system of `P`, relative to a notion
`recv c m i` of "`i` has received a 0-chain by `(c, m)`". -/
structure SafeWrt (recv : γ.Config → ℕ → Fin n → Prop) (P : γ.Protocol) : Prop where
  /-- (1) If `i` has not received a 0-chain by `(r, m)`, then `i` has the same local state at time
  `m` of some run in which all initial preferences are `1`. -/
  one : ∀ c : γ.Config, c.Valid → ∀ m i, ¬ recv c m i →
    ∃ c' : γ.Config, c'.Valid ∧ (∀ j, c'.init j = 1) ∧ γ.state P c' m i = γ.state P c m i
  /-- (2) If `¬K_i(⋀_j ¬(deciding_j = 0))` at `(r, m)` and `i` has not decided before round
  `m + 1`, then there is `(r', m)` with `r_i(m) = r'_i(m)`, `i` nonfaulty in `r'`, some agent `j`
  nonfaulty in `r'` deciding `0` in round `m + 1` of `r'`, and, if `m ≥ 1`, a run `r''` and an agent
  `j'` with `j, j'` nonfaulty in `r''`, `r'_j(m) = r''_j(m)` and `j'` deciding `0` in round `m` of
  `r''`. -/
  two : ∀ c : γ.Config, c.Valid → ∀ m i,
    ¬ Knows P i (γ.state P c m i) (fun c' m' => ∀ j, ¬ Deciding P c' m' j 0) →
    dec P c m i = none →
    ∃ c' : γ.Config, c'.Valid ∧ γ.state P c' m i = γ.state P c m i ∧ i ∈ c'.pat.N ∧
      ∃ j ∈ c'.pat.N, Deciding P c' m j 0 ∧
        (1 ≤ m → ∃ c'' : γ.Config, c''.Valid ∧ ∃ j', j ∈ c''.pat.N ∧ j' ∈ c''.pat.N ∧
          γ.state P c'' m j = γ.state P c' m j ∧ Deciding P c'' (m - 1) j' 0)

/-- Definition 6.2 (paper's 0-chains): `P0` is **safe** w.r.t. `γ` if the safety conditions hold
for every implementation of `P0`. -/
def SafeLit (γ : Context n) : Prop :=
  ∀ P : γ.Protocol, Implements P → SafeWrt (ReceivedChainLit P) P

/-- Definition 6.2 with repaired 0-chains. -/
def Safe (γ : Context n) : Prop :=
  ∀ P : γ.Protocol, Implements P → SafeWrt (ReceivedChain P) P

/-- An extra hypothesis of our version of Theorem 6.3: every local state of an undecided agent can
also occur, with the same initial preferences, in a run in which this agent is nonfaulty (agents
cannot detect their own faultiness before deciding). The paper's proof of Theorem 6.3 needs this
for the agent `i` it considers, which "may be faulty". -/
def NFConsistent (P : γ.Protocol) : Prop :=
  ∀ c : γ.Config, c.Valid → ∀ m i, dec P c m i = none →
    ∃ c' : γ.Config, c'.Valid ∧ c'.init = c.init ∧ i ∈ c'.pat.N ∧
      γ.state P c' m i = γ.state P c m i

/-- The system of `P` as a CSLib interpreted system (runs = admissible configurations). -/
noncomputable def toSystem (P : γ.Protocol) :
    Cslib.Knowledge.System (Fin n) {c : γ.Config // c.Valid} (fun _ => γ.L) where
  loc i r t := γ.state P r.1 t i
  nf r := ↑r.1.pat.N

/-- `Knows` is CSLib's knowledge operator `K_i` of the interpreted system `toSystem P`. -/
theorem knows_iff_K (P : γ.Protocol) (i : Fin n) (φ : γ.Config → ℕ → Prop)
    (c : γ.Config) (hc : c.Valid) (m : ℕ) :
    Knows P i (γ.state P c m i) φ ↔ (toSystem P).K i (fun r t => φ r.1 t) ⟨c, hc⟩ m := by
  rw [Cslib.Knowledge.System.K_iff]
  exact ⟨fun h r t ht => h r.1 r.2 t ht, fun h c' hc' t ht => h ⟨c', hc'⟩ t ht⟩

end Context

end Podc.OptimalEBAOmission
