import Cslib.Computability.Distributed.ContentOblivious.Compose
import Cslib.Foundations.Data.ZMod.Cyclic
import Mathlib

/-!
# The OR protocol of Lemma 5 (proof sketch)

*Brief Announcement: Toward Uniform Content-Oblivious Leader Election on General Graphs*,
PODC 2026, proof sketch of Lemma 5: once a leader `ℓ_C` of a cycle `C` is known, the nodes of `C`
can compute the OR of their input bits with `O(|C|)` pulses.

**Model.** Oriented ring `ZMod n` (`n ≥ 1`, wiring `Cslib.ContentOblivious.oriented n`:
`Port1 = true` is the clockwise port, linked to `Port0` of `v + 1`), asynchronous content-oblivious
pulses, adversarial delivery order (`Cslib.ContentOblivious.Step`), no failures, deterministic
nodes, exactly one leader, node `0`. The input of a node is `(isLeader, bit)`.

**Protocol** (the paper's description, made precise).
* The leader starts a clockwise pulse.
* A non-leader with input `0` forwards the first clockwise pulse clockwise and waits. A second
  clockwise pulse means output `0`; it forwards it clockwise and terminates. A counter-clockwise
  pulse (a reflection, or the leader's broadcast) means output `1`; it forwards it
  counter-clockwise and terminates.
* A non-leader with input `1` reflects the first clockwise pulse (sends it back
  counter-clockwise), outputs `1`, absorbs the next counter-clockwise pulse and terminates.
* Any non-leader whose *first* pulse is counter-clockwise outputs `1`, forwards it
  counter-clockwise and terminates (this also happens to nodes with input `1` lying clockwise after
  the first node with input `1`).
* The leader: if the reflection comes back (counter-clockwise), it outputs `1`, broadcasts it
  counter-clockwise and terminates (the broadcast is absorbed by the reflector). If its own pulse
  completes the cycle, then with own input `0` it outputs `0`, sends a second clockwise pulse and
  terminates when it returns; with own input `1` it outputs `1`, sends a counter-clockwise pulse and
  terminates when it returns. The last rule (the leader's own input) is not in the paper; the
  literal reading, in which the leader ignores its input, computes the wrong OR (`literal_wrong`).

**Proof method** (as in `ComputeOR` of the concurrent PODC 2026 counting paper): in every reachable
configuration, node `v` has completed `π v` receptions, on the ports of a fixed *role* `typ v`
determined by the inputs and the position of `v`. A pulse in transit always arrives at the expected
port of a node willing to read it: this follows from the channel inequalities between neighbours
(checked by `decide` over all pairs of adjacent roles) and, in one exceptional situation, from a
propagation argument around the ring.
-/

namespace Podc.ContentObliviousEulerian.OrProtocol

open Cslib.ContentOblivious Finset

/-- Local state of the OR protocol. -/
structure St where
  /-- input: is this node the leader -/
  ldr : Bool
  /-- the input bit used by the node -/
  b : Bool
  /-- number of receptions so far -/
  pc : ℕ
  /-- terminated -/
  fin : Bool
  /-- the output -/
  ans : Bool
  deriving DecidableEq

/-- Start-up. If `own = false` the leader ignores its own input bit (literal reading of the
paper). The leader sends one clockwise pulse. -/
def init (own : Bool) (a : Bool × Bool) : St × (Bool → ℕ) :=
  (⟨a.1, if a.1 then own && a.2 else a.2, 0, false, false⟩,
    if a.1 then onePulse true else fun _ => 0)

/-- Reaction to a pulse received on port `j`. -/
def recv (s : St) (j : Bool) : St × (Bool → ℕ) :=
  match s.pc with
  | 0 =>
    if j then
      -- first pulse is counter-clockwise (leader: the reflection): output 1, forward ccw, stop
      ({ s with pc := 1, fin := true, ans := true }, onePulse false)
    else if s.ldr then
      -- the leader's pulse completed the cycle
      if s.b then ({ s with pc := 1, ans := true }, onePulse false)
      else ({ s with pc := 1, ans := false }, onePulse true)
    else if s.b then ({ s with pc := 1, ans := true }, onePulse false) -- reflect
    else ({ s with pc := 1 }, onePulse true) -- forward cw
  | _ =>
    if s.ldr || s.b then ({ s with pc := s.pc + 1, fin := true }, fun _ => 0) -- absorb, stop
    else if j then ({ s with pc := s.pc + 1, fin := true, ans := true }, onePulse false)
    else ({ s with pc := s.pc + 1, fin := true, ans := false }, onePulse true)

/-- The port(s) on which the node waits. -/
def ready (s : St) (j : Bool) : Bool :=
  if s.fin then false else
  match s.pc with
  | 0 => true
  | _ => if s.ldr then j == s.b else if s.b then j else true

/-- The OR protocol as a procedure with input `(isLeader, bit)` and Boolean output. With
`own = false` the leader ignores its own bit. -/
abbrev proc (own : Bool) : Proc (Bool × Bool) Bool where
  State := St
  init := init own
  recv := recv
  ready := ready
  terminated s := s.fin
  result s := if s.fin then some s.ans else none
  terminated_eq s := by cases s.fin <;> simp

/-- The OR protocol of Lemma 5, with the leader using its own input. -/
abbrev orProc : Proc (Bool × Bool) Bool := proc true

/-- The literal reading of the paper: the leader ignores its own input. -/
abbrev literalProc : Proc (Bool × Bool) Bool := proc false

/-- The inputs on the ring with leader `0` and input bits `x`. -/
def inp {n : ℕ} (x : ZMod n → Bool) (v : ZMod n) : Bool × Bool := (decide (v = 0), x v)

/-! ## Roles -/

/-- Roles. All inputs `0`: `LZ` (leader), `NZ`. Leader input `1`, all others `0`: `LT`
(leader), `A`. Some non-leader with input `1`, the first one clockwise being `J`: `LR0`, `LR1`
(leader with input 0 / 1), `A` (the nodes strictly between the leader and `J`), `J`, `B0`, `B1`
(the nodes after `J`, input 0 / 1). -/
inductive Role
  | LZ | NZ | LT | LR0 | LR1 | A | J | B0 | B1
  deriving DecidableEq

namespace Role

instance : Fintype Role :=
  ⟨{LZ, NZ, LT, LR0, LR1, A, J, B0, B1}, by intro r; cases r <;> decide⟩

def ldr : Role → Bool
  | LZ | LT | LR0 | LR1 => true
  | _ => false

def b : Role → Bool
  | LT | LR1 | J | B1 => true
  | _ => false

/-- Number of receptions until termination. -/
def len : Role → ℕ
  | LR0 | LR1 | B0 | B1 => 1
  | _ => 2

/-- Port of the `m`-th reception (from `0`). -/
def hist : Role → ℕ → Bool
  | LZ, _ | NZ, _ => false
  | LR0, _ | LR1, _ | B0, _ | B1, _ => true
  | _, 0 => false
  | _, _ => true

/-- The node at which the propagation arguments start. -/
def center : Role → Bool
  | LZ | LT | J => true
  | _ => false

/-- Threshold for the propagation argument. -/
def θ : Role → ℕ
  | LZ | NZ => 0
  | A => 2
  | _ => 1

/-- The output of a node of this role. -/
def fans : Role → Bool
  | LZ | NZ => false
  | _ => true

/-- Adjacent roles `(typ v, typ (v + 1))`. -/
def Adj : Role → Role → Bool
  | LZ, NZ | NZ, NZ | NZ, LZ | LZ, LZ => true
  | LT, A | A, LT | LT, LT | A, A => true
  | LR0, A | LR1, A | LR0, J | LR1, J | A, J => true
  | J, B0 | J, B1 | J, LR0 | J, LR1 => true
  | B0, B0 | B0, B1 | B1, B0 | B1, B1 => true
  | B0, LR0 | B0, LR1 | B1, LR0 | B1, LR1 => true
  | _, _ => false

/-- State of a node of role `r` after `m` receptions. -/
def mk (r : Role) : ℕ → St
  | 0 => ⟨r.ldr, r.b, 0, false, false⟩
  | m + 1 => (recv (r.mk m) (r.hist m)).1

/-- Pulses sent on port `p` after `m` receptions. -/
def sentR (r : Role) : ℕ → Bool → ℕ
  | 0, p => (init false (r.ldr, false)).2 p
  | m + 1, p => r.sentR m p + (recv (r.mk m) (r.hist m)).2 p

/-- Pulses received on port `p` after `m` receptions. -/
def recvdR (r : Role) : ℕ → Bool → ℕ
  | 0, _ => 0
  | m + 1, p => r.recvdR m p + if r.hist m = p then 1 else 0

/-- Channel inequalities on the link from a node of role `r` with `m` receptions to its clockwise
neighbour of role `r'` with `m'` receptions. -/
def LC (r : Role) (m : ℕ) (r' : Role) (m' : ℕ) : Prop :=
  r'.recvdR m' false ≤ r.sentR m true ∧ r.recvdR m true ≤ r'.sentR m' false

instance (r : Role) (m : ℕ) (r' : Role) (m' : ℕ) : Decidable (LC r m r' m') := by
  unfold LC; infer_instance

/-- The same link without a pulse in transit. -/
def EQ (r : Role) (m : ℕ) (r' : Role) (m' : ℕ) : Prop :=
  r'.recvdR m' false = r.sentR m true ∧ r.recvdR m true = r'.sentR m' false

instance (r : Role) (m : ℕ) (r' : Role) (m' : ℕ) : Decidable (EQ r m r' m') := by
  unfold EQ; infer_instance

/-! ### Finite checks

Over all pairs of adjacent roles `r` (node `v`, `m` receptions) and `r'` (node `v + 1`, `m'`
receptions). The hypothesis `r.ldr → r'.ldr → m = m'` accounts for the 1-node ring. -/

theorem len_le : ∀ r : Role, r.len ≤ 2 := by decide

/-- A pulse in transit to `Port0` of `v + 1` is always expected. -/
theorem good0 : ∀ r r' : Role, ∀ m m' : Fin 3, Adj r r' = true → (m : ℕ) ≤ r.len →
    (m' : ℕ) ≤ r'.len → (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' →
    r'.recvdR m' false < r.sentR m true →
    (m' : ℕ) < r'.len ∧ r'.hist m' = false ∧ ready (r'.mk m') false = true ∧
      (r'.mk m').fin = false := by
  decide

/-- A pulse in transit to `Port1` of `v` is expected, except in one situation excluded by a
propagation argument. -/
theorem good1 : ∀ r r' : Role, ∀ m m' : Fin 3, Adj r r' = true → (m : ℕ) ≤ r.len →
    (m' : ℕ) ≤ r'.len → (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' →
    r.recvdR m true < r'.sentR m' false →
    ((m : ℕ) < r.len ∧ r.hist m = true ∧ ready (r.mk m) true = true ∧ (r.mk m).fin = false) ∨
      (r.center = true ∧ (m : ℕ) < θ r ∧ θ r' ≤ m') := by
  decide

theorem chainθ : ∀ r r' : Role, ∀ m m' : Fin 3, Adj r r' = true → r.center = false →
    (m : ℕ) ≤ r.len → (m' : ℕ) ≤ r'.len → LC r m r' m' → θ r ≤ m → θ r' ≤ m' := by
  decide

theorem chainDone : ∀ r r' : Role, ∀ m m' : Fin 3, Adj r r' = true → r'.center = false →
    (m : ℕ) ≤ r.len → (m' : ℕ) ≤ r'.len → EQ r m r' m' → (m : ℕ) = r.len → (m' : ℕ) = r'.len := by
  decide

theorem count : ∀ r : Role, ∀ m : Fin 3, (m : ℕ) ≤ r.len →
    r.sentR m false + r.sentR m true + (if r.center = true ∧ (m : ℕ) = r.len then 1 else 0) =
      r.recvdR m false + r.recvdR m true + (if r.ldr = true then 1 else 0) := by
  decide

theorem sent_le : ∀ r : Role, ∀ m : Fin 3, (m : ℕ) ≤ r.len →
    r.sentR m false + r.sentR m true ≤ 2 := by
  decide

theorem fin_mk : ∀ r : Role, ∀ m : Fin 3, (m : ℕ) ≤ r.len →
    ((r.mk m).fin = true ↔ (m : ℕ) = r.len) := by
  decide

theorem ans_mk : ∀ r : Role, (r.mk r.len).ans = r.fans := by decide

/-- Observation pattern at termination. -/
theorem recvd_done : ∀ r : Role,
    (r.fans = false → r.recvdR r.len false = 2 ∧ r.recvdR r.len true = 0) ∧
      (r.fans = true → r.recvdR r.len true = 1) := by
  decide

end Role

/-! ## The invariant -/

open Role

variable {n : ℕ} [NeZero n]

/-- The input bit stored by node `v` (the leader's own bit is dropped if `own = false`). -/
def eff (own : Bool) (x : ZMod n → Bool) (v : ZMod n) : Bool :=
  if v = 0 then own && x v else x v

/-- A role assignment compatible with the stored bits `e`, leader `0`. -/
structure Typing (e : ZMod n → Bool) (typ : ZMod n → Role) : Prop where
  adj : ∀ v, Adj (typ v) (typ (v + 1)) = true
  ldr : ∀ v, (typ v).ldr = decide (v = 0)
  bit : ∀ v, (typ v).b = e v
  uniqC : ∀ u v, (typ u).center = true → (typ v).center = true → u = v

/-- The configuration in which node `v` has role `typ v` and has completed `π v` receptions. -/
def cfgOf (typ : ZMod n → Role) (π : ZMod n → ℕ) : Config (ZMod n) St where
  st v := (typ v).mk (π v)
  sent p := (typ p.1).sentR (π p.1) p.2
  recvd p := (typ p.1).recvdR (π p.1) p.2

variable {own : Bool} {x : ZMod n → Bool} {typ : ZMod n → Role}

omit [NeZero n] in
lemma recvd_le {c : Config (ZMod n) St} (hr : (proc own).Reach (oriented n) (inp x) c)
    (p : ZMod n × Bool) : c.recvd p ≤ c.sent ((oriented n).peer p) :=
  Reach.recvd_le (W := oriented n) (A := (proc own).toAlgo) hr p

omit [NeZero n] in
lemma lc {π : ZMod n → ℕ} (hr : (proc own).Reach (oriented n) (inp x) (cfgOf typ π))
    (v : ZMod n) : LC (typ v) (π v) (typ (v + 1)) (π (v + 1)) := by
  constructor
  · have := recvd_le hr (v + 1, false)
    simpa [cfgOf] using this
  · have := recvd_le hr (v, true)
    simpa [cfgOf] using this

omit [NeZero n] in
lemma ldr_cond {e : ZMod n → Bool} (T : Typing e typ) (π : ZMod n → ℕ) (v : ZMod n) :
    (typ v).ldr = true → (typ (v + 1)).ldr = true → π v = π (v + 1) := fun h1 h2 => by
  rw [T.ldr] at h1 h2
  simp only [decide_eq_true_eq] at h1 h2
  rw [h1] at h2 ⊢; rw [h2]

/-- Every pulse in transit is expected: it arrives at the port of the next reception of a node
willing to read it. -/
theorem expected {e : ZMod n → Bool} (T : Typing e typ) {π : ZMod n → ℕ}
    (hπ : ∀ v, π v ≤ (typ v).len)
    (hr : (proc own).Reach (oriented n) (inp x) (cfgOf typ π)) (w : ZMod n) (j : Bool)
    (ht : (cfgOf typ π).recvd (w, j) < (cfgOf typ π).sent ((oriented n).peer (w, j))) :
    π w < (typ w).len ∧ (typ w).hist (π w) = j ∧ ready ((typ w).mk (π w)) j = true ∧
      ((typ w).mk (π w)).fin = false := by
  let f : ZMod n → Fin 3 := fun v => ⟨π v, by have := hπ v; have := len_le (typ v); omega⟩
  cases j
  · have hw : w - 1 + 1 = w := sub_add_cancel w 1
    have hlc := lc hr (w - 1)
    have hcond := ldr_cond T π (w - 1)
    have hadj := T.adj (w - 1)
    rw [hw] at hlc hcond hadj
    have ht' : (typ w).recvdR (π w) false < (typ (w - 1)).sentR (π (w - 1)) true := by
      simpa [cfgOf] using ht
    exact good0 (typ (w - 1)) (typ w) (f (w - 1)) (f w) hadj (hπ _) (hπ _) hcond hlc ht'
  · have ht' : (typ w).recvdR (π w) true < (typ (w + 1)).sentR (π (w + 1)) false := by
      simpa [cfgOf] using ht
    rcases good1 (typ w) (typ (w + 1)) (f w) (f (w + 1)) (T.adj w) (hπ _) (hπ _)
      (ldr_cond T π w) (lc hr w) ht' with h | h
    · exact h
    · exfalso
      obtain ⟨hc, h1, h2⟩ := h
      have := ZMod.chain_cw_all (fun u => θ (typ u) ≤ π u) w (fun u hu hS => by
        have hnc : (typ u).center = false := by
          by_contra hc'; exact hu (T.uniqC _ _ (by simpa using hc') hc)
        exact chainθ (typ u) (typ (u + 1)) (f u) (f (u + 1)) (T.adj u) hnc (hπ _) (hπ _)
          (lc hr u) hS) h2 w
      exact absurd this (by simpa [f] using h1)

omit [NeZero n] in
lemma deliver_cfgOf {π : ZMod n → ℕ} (w : ZMod n) :
    deliver (proc own).toAlgo (cfgOf typ π) w ((typ w).hist (π w)) =
      cfgOf typ (Function.update π w (π w + 1)) := by
  ext v
  · by_cases h : v = w
    · subst h; simp [deliver, cfgOf, Role.mk]
    · simp [deliver, cfgOf, h]
  · rcases v with ⟨v, p⟩
    by_cases h : v = w
    · subst h; simp [deliver, cfgOf, Role.sentR]
    · simp [deliver, cfgOf, h]
  · rcases v with ⟨v, p⟩
    by_cases h : v = w
    · subst h; simp [deliver, cfgOf, Role.recvdR, eq_comm]
    · simp [deliver, cfgOf, h]

/-- **Invariant**: every reachable configuration is of the form `cfgOf typ π`. -/
theorem reach_inv (T : Typing (eff own x) typ) {c : Config (ZMod n) St}
    (hc : (proc own).Reach (oriented n) (inp x) c) :
    ∃ π : ZMod n → ℕ, (∀ v, π v ≤ (typ v).len) ∧ c = cfgOf typ π := by
  refine Prog.Reach.induction (motive := fun c => ∃ π : ZMod n → ℕ,
    (∀ v, π v ≤ (typ v).len) ∧ c = cfgOf typ π) ?_ ?_ hc
  · refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_⟩
    ext v
    · simp only [Prog.initCfg, cfgOf, Role.mk, init, inp, T.ldr v, T.bit v, eff]
      by_cases h : v = 0 <;> simp [h]
    · simp [Prog.initCfg, cfgOf, Role.sentR, init, inp, T.ldr]
    · simp [Prog.initCfg, cfgOf, Role.recvdR]
  · intro c c' hr hs ih
    obtain ⟨π, hπ, rfl⟩ := ih
    obtain ⟨w, j, hen⟩ := hs
    obtain ⟨h3, hj, -⟩ := expected T hπ hr w j hen.2.2
    subst hj
    refine ⟨Function.update π w (π w + 1), fun v => ?_, deliver_cfgOf w⟩
    rw [Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact hπ v

lemma totalSent_cfgOf (π : ZMod n → ℕ) :
    totalSent (cfgOf typ π) = ∑ v, ((typ v).sentR (π v) false + (typ v).sentR (π v) true) := by
  simp [totalSent, sum_ports, cfgOf]

lemma totalRecvd_cfgOf (π : ZMod n → ℕ) :
    totalRecvd (cfgOf typ π) =
      ∑ v, ((typ v).recvdR (π v) false + (typ v).recvdR (π v) true) := by
  simp [totalRecvd, sum_ports, cfgOf]

lemma totalSent_le' (π : ZMod n → ℕ) (hπ : ∀ v, π v ≤ (typ v).len) :
    totalSent (cfgOf typ π) ≤ 2 * n := by
  rw [totalSent_cfgOf]
  calc ∑ v, ((typ v).sentR (π v) false + (typ v).sentR (π v) true) ≤ ∑ _v : ZMod n, 2 :=
        sum_le_sum fun v _ => sent_le (typ v)
          ⟨π v, by have := hπ v; have := len_le (typ v); omega⟩ (hπ v)
    _ = 2 * n := by simp [ZMod.card, mul_comm]

/-- Final configurations: quiescent, and every node has completed all its receptions. -/
theorem final_spec {e : ZMod n → Bool} (T : Typing e typ) {π : ZMod n → ℕ}
    (hπ : ∀ v, π v ≤ (typ v).len)
    (hr : (proc own).Reach (oriented n) (inp x) (cfgOf typ π))
    (hf : (proc own).Final (oriented n) (cfgOf typ π)) :
    (proc own).Quiescent (oriented n) (cfgOf typ π) ∧ ∀ v, π v = (typ v).len := by
  let f : ZMod n → Fin 3 := fun v => ⟨π v, by have := hπ v; have := len_le (typ v); omega⟩
  have hq : (proc own).Quiescent (oriented n) (cfgOf typ π) := by
    intro p
    by_contra hne
    have hlt := lt_of_le_of_ne (recvd_le hr p) hne
    obtain ⟨-, -, hrd, hfin⟩ := expected T hπ hr p.1 p.2 hlt
    exact hf p.1 p.2 ⟨hfin, hrd, hlt⟩
  refine ⟨hq, ?_⟩
  -- counting: some center has terminated
  have hcount : totalSent (cfgOf typ π) +
      ∑ v, (if (typ v).center = true ∧ π v = (typ v).len then 1 else 0) =
      totalRecvd (cfgOf typ π) + ∑ v : ZMod n, (if (typ v).ldr = true then 1 else 0) := by
    rw [totalSent_cfgOf, totalRecvd_cfgOf, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun v _ => count (typ v) (f v) (hπ v)
  have hl : ∑ v : ZMod n, (if (typ v).ldr = true then 1 else 0) = 1 := by
    simp [T.ldr]
  rw [← Quiescent.totalRecvd_eq hq, hl] at hcount
  have hpos : 0 < ∑ v, (if (typ v).center = true ∧ π v = (typ v).len then 1 else 0) := by
    omega
  obtain ⟨w, -, hw⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  have hw' : (typ w).center = true ∧ π w = (typ w).len := by
    by_contra h; simp [h] at hw
  have heq : ∀ u, EQ (typ u) (π u) (typ (u + 1)) (π (u + 1)) := fun u => by
    constructor
    · have := hq (u + 1, false); simpa [cfgOf] using this
    · have := hq (u, true); simpa [cfgOf] using this
  refine ZMod.chain_cw_all (fun u => π u = (typ u).len) (w - 1) (fun u hu hS => ?_)
    (by simp only [sub_add_cancel]; exact hw'.2)
  have hnc : (typ (u + 1)).center = false := by
    by_contra hc
    have e : u + 1 = w := T.uniqC _ _ (by simpa using hc) hw'.1
    exact hu (by rw [← e, add_sub_cancel_right])
  exact chainDone (typ u) (typ (u + 1)) (f u) (f (u + 1)) (T.adj u) hnc (hπ _) (hπ _)
    (heq u) hS

/-! ## The roles of the nodes -/

section typing

variable (e : ZMod n → Bool)

/-- Node `k` (as a number) is a non-leader with stored bit `1`. -/
def SomeTrue (k : ℕ) : Prop := 0 < k ∧ k < n ∧ e (k : ZMod n) = true

instance : DecidablePred (SomeTrue e) := fun k => by unfold SomeTrue; infer_instance

open Classical in
/-- The role of each node, given the stored bits `e` (leader `0`). -/
noncomputable def typOf (v : ZMod n) : Role :=
  if h : ∃ k, SomeTrue e k then
    if v.val = 0 then (if e 0 then .LR1 else .LR0)
    else if v.val < Nat.find h then .A
    else if v.val = Nat.find h then .J
    else if e v then .B1 else .B0
  else if v.val = 0 then (if e 0 then .LT else .LZ)
  else if e 0 then .A else .NZ

lemma natCast_val' (v : ZMod n) : ((v.val : ℕ) : ZMod n) = v := ZMod.natCast_zmod_val v

lemma succ_val (v : ZMod n) : (v.val + 1 < n ∧ (v + 1).val = v.val + 1) ∨
    (v.val + 1 = n ∧ (v + 1).val = 0) := by
  have h : (v + 1).val = (v.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  have := ZMod.val_lt v
  by_cases hc : v.val + 1 < n
  · left; exact ⟨hc, by rw [h, Nat.mod_eq_of_lt hc]⟩
  · right
    have e : v.val + 1 = n := by omega
    exact ⟨e, by rw [h, e, Nat.mod_self]⟩

variable {e}

omit [NeZero n] in
lemma typOf_of_ex (hex : ∃ k, SomeTrue e k) (v : ZMod n) :
    typOf e v = if v.val = 0 then (if e 0 then .LR1 else .LR0)
      else if v.val < Nat.find hex then .A else if v.val = Nat.find hex then .J
      else if e v then .B1 else .B0 := by
  simp only [typOf, hex, dite_true]

omit [NeZero n] in
lemma typOf_of_not_ex (hex : ¬ ∃ k, SomeTrue e k) (v : ZMod n) :
    typOf e v = if v.val = 0 then (if e 0 then .LT else .LZ) else if e 0 then .A else .NZ := by
  simp only [typOf, hex, dite_false]

lemma eq_false_of_not_ex (hex : ¬ ∃ k, SomeTrue e k) (v : ZMod n) (hv : v.val ≠ 0) :
    e v = false := by
  by_contra h
  exact hex ⟨v.val, Nat.pos_of_ne_zero hv, ZMod.val_lt v, by rw [natCast_val']; simpa using h⟩

variable (e) in
theorem typing : Typing e (typOf e) := by
  by_cases hex : ∃ k, SomeTrue e k
  · have hjs : SomeTrue e (Nat.find hex) := Nat.find_spec hex
    have hmin : ∀ k < Nat.find hex, ¬ SomeTrue e k := fun k hk => Nat.find_min hex hk
    obtain ⟨hj0, hjn, hje⟩ := hjs
    refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun u v hu hv => ?_⟩
    · have := succ_val v
      rw [typOf_of_ex hex, typOf_of_ex hex]
      split_ifs <;> first | rfl | omega
    · have hv0 : decide (v = 0) = decide (v.val = 0) := by simp [ZMod.val_eq_zero]
      rw [typOf_of_ex hex, hv0]
      split_ifs <;> simp_all [Role.ldr]
    · rw [typOf_of_ex hex]
      by_cases h1 : v.val = 0
      · have : v = 0 := (ZMod.val_eq_zero v).1 h1
        subst this
        cases h : e 0 <;> simp [Role.b]
      · simp only [h1, ite_false]
        split_ifs with h2 h3 h4
        · have := hmin _ h2
          simp only [SomeTrue, natCast_val', not_and, Bool.not_eq_true] at this
          rw [this (Nat.pos_of_ne_zero h1) (ZMod.val_lt v)]; rfl
        · have hv : ((v.val : ℕ) : ZMod n) = ((Nat.find hex : ℕ) : ZMod n) := by rw [h3]
          rw [natCast_val'] at hv; rw [hv, hje]; rfl
        · rw [h4]; rfl
        · simp only [Bool.not_eq_true] at h4; rw [h4]; rfl
    · have hcen : ∀ w, (typOf e w).center = true → w.val = Nat.find hex := by
        intro w hw
        rw [typOf_of_ex hex] at hw
        split_ifs at hw <;> first | assumption | simp [Role.center] at hw
      exact ZMod.val_injective n ((hcen u hu).trans (hcen v hv).symm)
  · refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun u v hu hv => ?_⟩
    · have := succ_val v
      rw [typOf_of_not_ex hex, typOf_of_not_ex hex]
      split_ifs <;> rfl
    · have hv0 : decide (v = 0) = decide (v.val = 0) := by simp [ZMod.val_eq_zero]
      rw [typOf_of_not_ex hex, hv0]
      split_ifs <;> simp_all [Role.ldr]
    · rw [typOf_of_not_ex hex]
      by_cases h1 : v.val = 0
      · have : v = 0 := (ZMod.val_eq_zero v).1 h1
        subst this
        cases h : e 0 <;> simp [Role.b]
      · rw [eq_false_of_not_ex hex v h1]
        simp only [h1, ite_false]; split_ifs <;> rfl
    · have hcen : ∀ w, (typOf e w).center = true → w = 0 := by
        intro w hw
        rw [typOf_of_not_ex hex] at hw
        rw [← ZMod.val_eq_zero]
        split_ifs at hw <;> first | assumption | simp [Role.center] at hw
      rw [hcen u hu, hcen v hv]

lemma fans_typOf (v : ZMod n) : (typOf e v).fans = decide (∃ v, e v = true) := by
  by_cases hex : ∃ k, SomeTrue e k
  · have h' : ∃ v, e v = true := ⟨_, (Nat.find_spec hex).2.2⟩
    rw [typOf_of_ex hex, decide_eq_true h']
    split_ifs <;> rfl
  · rw [typOf_of_not_ex hex]
    by_cases h0 : e 0 = true
    · rw [decide_eq_true ⟨0, h0⟩]; simp only [h0, ite_true]; split_ifs <;> rfl
    · have h' : ¬ ∃ v, e v = true := by
        rintro ⟨v, hv⟩
        by_cases h1 : v.val = 0
        · rw [(ZMod.val_eq_zero v).1 h1] at hv; exact h0 hv
        · rw [eq_false_of_not_ex hex v h1] at hv; cases hv
      rw [decide_eq_false h']; simp only [h0, ite_false, Bool.false_eq_true]; split_ifs <;> rfl

end typing

/-! ## Results for both variants (`own = true`: our protocol; `own = false`: literal reading) -/

section general

variable (own : Bool) (x : ZMod n → Bool)

theorem totalSent_le_gen {c : Config (ZMod n) St}
    (hc : (proc own).Reach (oriented n) (inp x) c) : totalSent c ≤ 2 * n := by
  obtain ⟨π, hπ, rfl⟩ := reach_inv (typing (eff own x)) hc
  exact totalSent_le' π hπ

theorem final_gen {c : Config (ZMod n) St} (hc : (proc own).Reach (oriented n) (inp x) c)
    (hf : (proc own).Final (oriented n) c) :
    ∃ π : ZMod n → ℕ, c = cfgOf (typOf (eff own x)) π ∧
      (proc own).Quiescent (oriented n) c ∧ ∀ v, π v = (typOf (eff own x) v).len := by
  obtain ⟨π, hπ, rfl⟩ := reach_inv (typing (eff own x)) hc
  exact ⟨π, rfl, final_spec (typing _) hπ hc hf⟩

theorem result_gen {c : Config (ZMod n) St} (hc : (proc own).Reach (oriented n) (inp x) c)
    (hf : (proc own).Final (oriented n) c) (v : ZMod n) :
    (proc own).result (c.st v) = some (decide (∃ v, eff own x v = true)) := by
  obtain ⟨π, rfl, -, hπ⟩ := final_gen own x hc hf
  set r := typOf (eff own x) v
  have hst : (cfgOf (typOf (eff own x)) π).st v = r.mk r.len := by simp [cfgOf, hπ v, r]
  have h1 : (r.mk r.len).fin = true :=
    (fin_mk r ⟨r.len, by have := len_le r; omega⟩ (by simp)).2 rfl
  show (if ((cfgOf (typOf (eff own x)) π).st v).fin then _ else _) = _
  rw [hst]; simp only [h1, ite_true, ans_mk, r, fans_typOf]

/-- Every execution can be completed: there is a reachable final configuration. -/
theorem exists_final_gen : ∃ c, (proc own).Reach (oriented n) (inp x) c ∧
    (proc own).Final (oriented n) c := by
  obtain ⟨c, h1, h2⟩ := Cslib.ContentOblivious.exists_final (W := oriented n)
    (A := (proc own).toAlgo) (id := fun v => Encodable.encode (inp x v)) (B := 2 * n)
    (fun c hc => totalSent_le_gen own x hc) Relation.ReflTransGen.refl
  exact ⟨c, h1, h2⟩

end general

omit [NeZero n] in
lemma eff_true (x : ZMod n → Bool) : eff true x = x := by
  funext v; by_cases h : v = 0 <;> simp [eff, h]

/-! ## Lemma 5 (proof sketch, OR protocol) -/

variable (x : ZMod n → Bool)

/-- **Lemma 5 (proof sketch, OR protocol)**, message complexity: on the oriented ring with leader
`0`, no execution of the OR protocol sends more than `2n` pulses. -/
theorem orProc_totalSent_le {c : Config (ZMod n) St}
    (hc : orProc.Reach (oriented n) (inp x) c) : totalSent c ≤ 2 * n :=
  totalSent_le_gen true x hc

/-- **Lemma 5 (proof sketch, OR protocol)**, correctness: every final configuration (no pulse
can be consumed) is quiescent, all nodes have terminated, and every node outputs the OR of all
inputs. -/
theorem orProc_final {c : Config (ZMod n) St} (hc : orProc.Reach (oriented n) (inp x) c)
    (hf : orProc.Final (oriented n) c) :
    orProc.Quiescent (oriented n) c ∧ (∀ v, orProc.terminated (c.st v) = true) ∧
      ∀ v, orProc.result (c.st v) = some (decide (∃ v, x v = true)) := by
  have hres := result_gen true x hc hf
  rw [eff_true] at hres
  refine ⟨(final_gen true x hc hf).choose_spec.2.1, fun v => ?_, hres⟩
  rw [orProc.terminated_eq, hres v]; rfl

/-- **Lemma 5 (proof sketch, OR protocol)**, in the `Returns` form of `Cslib.ContentOblivious`. -/
theorem orProc_returns :
    orProc.Returns (oriented n) (inp x) (fun _ => decide (∃ v, x v = true)) :=
  fun _ hc hf v => (orProc_final x hc hf).2.2 v

/-- Non-vacuity: the OR protocol always reaches a final configuration (every maximal execution
is finite, `no_infinite_execution`, and ends in such a configuration). -/
theorem orProc_exists_final : ∃ c, orProc.Reach (oriented n) (inp x) c ∧
    orProc.Final (oriented n) c :=
  exists_final_gen true x

/-- **Lemma 5 (proof sketch, OR protocol)**, observations: if all inputs are `0`, every node
received exactly two pulses, both clockwise (on `Port0`); otherwise every node received exactly
one counter-clockwise pulse (on `Port1`). -/
theorem orProc_observations {c : Config (ZMod n) St} (hc : orProc.Reach (oriented n) (inp x) c)
    (hf : orProc.Final (oriented n) c) :
    ((∀ v, x v = false) → ∀ v, c.recvd (v, false) = 2 ∧ c.recvd (v, true) = 0) ∧
      ((∃ v, x v = true) → ∀ v, c.recvd (v, true) = 1) := by
  obtain ⟨π, rfl, -, hπ⟩ := final_gen true x hc hf
  refine ⟨fun h v => ?_, fun h v => ?_⟩
  · have : ¬ ∃ v, x v = true := by rintro ⟨v, hv⟩; simp [h v] at hv
    have := (recvd_done (typOf (eff true x) v)).1 (by rw [fans_typOf, eff_true, decide_eq_false this])
    simpa [cfgOf, hπ v] using this
  · have := (recvd_done (typOf (eff true x) v)).2 (by rw [fans_typOf, eff_true, decide_eq_true h])
    simpa [cfgOf, hπ v] using this

/-- Remark: the literal reading of the proof sketch, in which the leader ignores its own input,
is wrong when only the leader has input `1`: the pulse completes the cycle and every node outputs
`0`, although the OR is `1`. -/
theorem literal_wrong :
    (∃ v : ZMod n, decide (v = 0) = true) ∧
    (∃ c, literalProc.Reach (oriented n) (inp fun v => decide (v = 0)) c ∧
      literalProc.Final (oriented n) c) ∧
    ∀ c, literalProc.Reach (oriented n) (inp fun v => decide (v = 0)) c →
      literalProc.Final (oriented n) c → ∀ v, literalProc.result (c.st v) = some false := by
  refine ⟨⟨0, by simp⟩, exists_final_gen false _, fun c hc hf v => ?_⟩
  rw [result_gen false _ hc hf v]
  congr 1
  simp [eff]

end Podc.ContentObliviousEulerian.OrProtocol
