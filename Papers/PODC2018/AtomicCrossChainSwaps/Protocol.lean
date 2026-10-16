import Papers.PODC2018.AtomicCrossChainSwaps.Atomicity

/-!
# §4: the hashed-timelock swap protocol as an executable model

**Time.** Discrete, in units of `Δ`; the protocol starts at time `0`. In round `t` every party
observes the state of all blockchains at time `t` and submits actions; they take effect at time
`t + 1` (one `Δ` = publish + confirm, as in Figures 1–2 of the paper: Alice's first contract is
in place at `Δ`). Conforming parties are thus lock-step.

**Contracts.** One contract per arc, published by the arc's head; we only model correct
contracts (a conforming party treats an incorrect one as missing). Every arc carries one
hashlock per leader `ℓ ∈ L`. A call `unlock(ℓ, p)` on arc `(u, v)`, made by the counterparty
`v`, succeeds iff the contract is already published, `p` is a path (paper's §2.1 sense) from `v`
to `ℓ`, and the call takes effect no later than the deadline `B + |p|` (the paper has `B = diam D`;
Figure 2 triggers contracts exactly at their timeouts, so the deadline is inclusive). An arc is
triggered when all its hashlocks are unlocked (`claim` has no deadline).

**Keys and the adversary.** Hashkeys are symbolic: a key for `ℓ` is the path `p` (the secret
`s_ℓ` with the nested signatures of the vertices of `p`). Every submitted key is public (the
contract call is on a public ledger), including keys of failed calls, and so are all its suffixes
(the inner signatures). The deviating coalition `C` shares knowledge and can extend a key it knows
by signing as any of its members, and knows the secrets of its leaders; it can never sign for a
conforming party (unforgeable signatures). It publishes contracts on its own arcs whenever it
likes (or never) and makes arbitrary unlock calls on arcs whose counterparty it controls. If
`rush` is set, its calls in round `t` may already use keys that conforming parties submit in the
same round (front-running).

**Conforming behaviour** (§4.5). A leader publishes contracts on all its leaving arcs in round
`0`; a follower does so in the first round in which all its entering arcs have contracts. A leader
releases its secret (calls `unlock(ℓ, (ℓ))` on all entering arcs) in the first round in which all
its entering arcs have contracts. A party `v` that sees hashlock `ℓ ≠ v` unlocked on a leaving arc
by key `p` (for the first time) calls `unlock(ℓ, v + p)` on its entering arcs.

Two variants: `fixed = false` is the paper's protocol read literally (the forwarding is done once,
at the first observation, on the entering arcs that have contracts at that moment). `fixed = true`
is our repair: a leader releases its secret only if its own key can still meet its deadline
(`t + 1 ≤ B`), and forwarding is repeated for entering contracts that appear later (while the
forwarded key is still valid).
-/

namespace AtomicSwap

/-- Hashkey validity for hashlock `ℓ` on an arc entering `v`: `p` is a path from `v` to `ℓ`. -/
def IsKey {V : Type*} (D : Digraph V) (ℓ v : V) (p : List V) : Prop :=
  IsPath D p ∧ p.head? = some v ∧ p.getLast? = some ℓ

/-- Deadline of a key with path `p`: `B + |p|`. -/
def dl {V : Type*} (B : ℕ) (p : List V) : ℕ := B + (p.length - 1)

/-- Parameters of a run of the protocol. -/
structure Setting (V : Type*) where
  /-- the swap digraph -/
  D : Digraph V
  [dec : DecidableRel D.Adj]
  /-- the leaders -/
  L : Finset V
  /-- the base timeout: hashkey `p` expires at `B + |p|` (the paper: `B = diam D`) -/
  B : ℕ
  /-- `false`: the paper's protocol; `true`: the repaired protocol -/
  fixed : Bool
  /-- whether the adversary may front-run (use keys submitted in the same round) -/
  rush : Bool

attribute [instance] Setting.dec

/-- The state of all blockchains plus the (public) log, and the local memory of conforming parties. -/
structure St (V : Type*) where
  /-- time at which the contract on arc `(u, v)` was published -/
  con : V → V → Option ℕ
  /-- `unl u v ℓ = some (τ, p)`: hashlock `ℓ` on `(u, v)` was unlocked at time `τ` with key `p` -/
  unl : V → V → V → Option (ℕ × List V)
  /-- all keys submitted (successfully or not) in `unlock` calls on `(u, v)` for hashlock `ℓ` -/
  sub : V → V → V → List (List V)
  /-- round in which a conforming leader released its secret -/
  rel : V → Option ℕ
  /-- the key with which a conforming party first saw hashlock `ℓ` unlocked on a leaving arc -/
  first : V → V → Option (List V)
  /-- literal protocol: whether `v` has already forwarded hashlock `ℓ` -/
  fwd : V → V → Bool

/-- What the adversary (and the scheduler) chooses in a round. -/
structure Moves (V : Type*) where
  /-- contracts published by the coalition -/
  pubs : List (V × V)
  /-- unlock calls `(u, v, ℓ, p)` on arc `(u, v)`, by the coalition member `v` -/
  calls : List (V × V × V × List V)
  /-- tie-breaking: which unlocked leaving arc `(v, w)` a conforming `v` takes its first key from -/
  pick : V → V → V

namespace Setting

variable {V : Type*} [DecidableEq V] [Fintype V] (P : Setting V) (C : Finset V)

instance (ℓ v : V) : DecidablePred (IsKey P.D ℓ v) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Initial state. -/
def _root_.AtomicSwap.St.init : St V :=
  ⟨fun _ _ => none, fun _ _ _ => none, fun _ _ _ => [], fun _ => none, fun _ _ => none,
    fun _ _ => false⟩

/-- All arcs entering `v` carry a contract. -/
def AllIn (s : St V) (v : V) : Prop := ∀ u, P.D.Adj u v → (s.con u v).isSome

instance (s : St V) (v : V) : Decidable (P.AllIn s v) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A conforming party publishes its leaving contracts in round `t`. -/
def Publishes (t : ℕ) (s : St V) (u : V) : Prop :=
  u ∉ C ∧ (u ∈ P.L → t = 0) ∧ (u ∉ P.L → P.AllIn s u)

instance (t : ℕ) (s : St V) (u : V) : Decidable (P.Publishes C t s u) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A conforming leader releases its secret in round `t`. -/
def Releases (t : ℕ) (s : St V) (v : V) : Prop :=
  v ∉ C ∧ v ∈ P.L ∧ s.rel v = none ∧ P.AllIn s v ∧ (P.fixed = true → t + 1 ≤ P.B)

instance (t : ℕ) (s : St V) (v : V) : Decidable (P.Releases C t s v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The first key for hashlock `ℓ` that `v` has observed on a leaving arc (by round `t`). -/
def obs (s : St V) (m : Moves V) (v ℓ : V) : Option (List V) :=
  match s.first v ℓ with
  | some p => some p
  | none => if P.D.Adj v (m.pick v ℓ) then (s.unl v (m.pick v ℓ) ℓ).map Prod.snd else none

/-- The key a conforming `v` submits for hashlock `ℓ` on the entering arc `(u, v)` in round `t`. -/
def confKey (t : ℕ) (s : St V) (m : Moves V) (u v ℓ : V) : Option (List V) :=
  if v ∈ C ∨ ¬ P.D.Adj u v ∨ ℓ ∉ P.L then none
  else if ℓ = v then (if P.Releases C t s v then some [v] else none)
  else match P.obs s m v ℓ with
    | none => none
    | some p =>
      if P.fixed then
        (if v ∉ p ∧ (s.con u v).isSome ∧ s.unl u v ℓ = none ∧ t + 1 ≤ dl P.B (v :: p) then
          some (v :: p) else none)
      else (if s.fwd v ℓ = false ∧ (s.con u v).isSome then some (v :: p) else none)

/-- A call `unlock(ℓ, p)` on `(u, v)` made in round `t` succeeds. -/
def Ok (t : ℕ) (s : St V) (u v ℓ : V) (p : List V) : Prop :=
  (s.con u v).isSome ∧ ℓ ∈ P.L ∧ IsKey P.D ℓ v p ∧ t + 1 ≤ dl P.B p

instance (t : ℕ) (s : St V) (u v ℓ : V) (p : List V) : Decidable (P.Ok t s u v ℓ p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Whether an adversarial call is on arc `(u, v)` for hashlock `ℓ`. -/
def IsOn (u v ℓ : V) (c : V × V × V × List V) : Bool := c.1 = u ∧ c.2.1 = v ∧ c.2.2.1 = ℓ

/-- The key that unlocks hashlock `ℓ` on `(u, v)` in round `t`, if any. -/
def newKey (t : ℕ) (s : St V) (m : Moves V) (u v ℓ : V) : Option (List V) :=
  if v ∈ C then
    ((m.calls.filter (IsOn u v ℓ)).map (·.2.2.2)).find? (fun p => decide (P.Ok t s u v ℓ p))
  else (P.confKey C t s m u v ℓ).filter (fun p => decide (P.Ok t s u v ℓ p))

/-- Keys submitted on `(u, v)` for `ℓ` in round `t`. -/
def roundKeys (t : ℕ) (s : St V) (m : Moves V) (u v ℓ : V) : List (List V) :=
  (P.confKey C t s m u v ℓ).toList ++ (m.calls.filter (IsOn u v ℓ)).map (·.2.2.2)

/-- Public knowledge at state `s`: suffixes of submitted keys. -/
def _root_.AtomicSwap.St.Known (s : St V) (ℓ : V) (q : List V) : Prop := ∃ u v, ∃ p ∈ s.sub u v ℓ, q <:+ p

/-- Knowledge available to the adversary in round `t` (with front-running if `rush`). -/
def KnownR (t : ℕ) (s : St V) (m : Moves V) (ℓ : V) (q : List V) : Prop :=
  s.Known ℓ q ∨ (P.rush = true ∧ ∃ u v, ∃ p ∈ (P.confKey C t s m u v ℓ).toList, q <:+ p)

/-- Keys the coalition can produce from the keys `K` it knows: suffix-closed knowledge, extended by
signatures of coalition members; the bare secret `[ℓ]` only if `ℓ ∈ C`. -/
def Derivable (K : List V → Prop) (ℓ : V) : List V → Prop
  | [] => False
  | [c] => K [c] ∨ (c ∈ C ∧ c = ℓ)
  | c :: d :: q => K (c :: d :: q) ∨ (c ∈ C ∧ Derivable K ℓ (d :: q))

instance (s : St V) (ℓ : V) (q : List V) : Decidable (s.Known ℓ q) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (t : ℕ) (s : St V) (m : Moves V) (ℓ : V) : DecidablePred (P.KnownR C t s m ℓ) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Decidability of `Derivable`. -/
def decDerivable (K : List V → Prop) [DecidablePred K] (ℓ : V) :
    (q : List V) → Decidable (Derivable C K ℓ q)
  | [] => by unfold Derivable; infer_instance
  | [_] => by unfold Derivable; infer_instance
  | _ :: d :: q => by unfold Derivable; haveI := decDerivable K ℓ (d :: q); infer_instance

instance (K : List V → Prop) [DecidablePred K] (ℓ : V) : DecidablePred (Derivable C K ℓ) :=
  decDerivable C K ℓ

/-- Validity of the adversary's moves (and of the scheduler's tie-breaking) in round `t`. -/
def Valid (t : ℕ) (s : St V) (m : Moves V) : Prop :=
  (∀ e ∈ m.pubs, e.1 ∈ C) ∧
  (∀ c ∈ m.calls, c.2.1 ∈ C ∧ Derivable C (P.KnownR C t s m c.2.2.1) c.2.2.1 c.2.2.2) ∧
  (∀ v ℓ, v ∉ C → ℓ ∈ P.L → ℓ ≠ v → s.first v ℓ = none →
    (∃ w, P.D.Adj v w ∧ (s.unl v w ℓ).isSome) →
    P.D.Adj v (m.pick v ℓ) ∧ (s.unl v (m.pick v ℓ) ℓ).isSome)

instance (t : ℕ) (s : St V) (m : Moves V) : Decidable (P.Valid C t s m) := by
  unfold Valid
  haveI : ∀ c : V × V × V × List V,
      Decidable (Derivable C (P.KnownR C t s m c.2.2.1) c.2.2.1 c.2.2.2) :=
    fun c => decDerivable C _ _ _
  haveI h1 : Decidable (∀ e ∈ m.pubs, e.1 ∈ C) := inferInstance
  haveI h2 : Decidable (∀ c ∈ m.calls, c.2.1 ∈ C ∧
      Derivable C (P.KnownR C t s m c.2.2.1) c.2.2.1 c.2.2.2) := inferInstance
  haveI h3 : ∀ v ℓ : V, Decidable (∃ w, P.D.Adj v w ∧ (s.unl v w ℓ).isSome = true) :=
    fun _ _ => inferInstance
  infer_instance

/-- One round. -/
def step (t : ℕ) (s : St V) (m : Moves V) : St V where
  con u v := (s.con u v).or
    (if P.D.Adj u v ∧ (P.Publishes C t s u ∨ (u ∈ C ∧ (u, v) ∈ m.pubs)) then some (t + 1)
      else none)
  unl u v ℓ := (s.unl u v ℓ).or ((P.newKey C t s m u v ℓ).map fun p => (t + 1, p))
  sub u v ℓ := s.sub u v ℓ ++ P.roundKeys C t s m u v ℓ
  rel v := (s.rel v).or (if P.Releases C t s v then some t else none)
  first v ℓ := if v ∉ C ∧ ℓ ∈ P.L ∧ ℓ ≠ v then P.obs s m v ℓ else none
  fwd v ℓ := s.fwd v ℓ || (if v ∉ C ∧ ℓ ∈ P.L ∧ ℓ ≠ v then P.obs s m v ℓ else none).isSome

/-- The execution determined by the adversary's schedule. -/
def run (sch : ℕ → Moves V) : ℕ → St V
  | 0 => St.init
  | t + 1 => P.step C t (run sch t) (sch t)

/-- An admissible schedule for coalition `C`. -/
def ValidSched (sch : ℕ → Moves V) : Prop := ∀ t, P.Valid C t (P.run C sch t) (sch t)

/-- Arc `(u, v)` is triggered in state `s`: all its hashlocks are unlocked. -/
def Trig (s : St V) (u v : V) : Prop := ∀ ℓ ∈ P.L, (s.unl u v ℓ).isSome

instance (s : St V) (u v : V) : Decidable (P.Trig s u v) :=
  inferInstanceAs (Decidable (∀ ℓ ∈ P.L, _))

/-- The final outcome: the arcs that are eventually triggered. -/
def Final (sch : ℕ → Moves V) (u v : V) : Prop := ∃ t, P.Trig (P.run C sch t) u v

open Classical in
/-- The protocol as an abstract swap game (§3): the outcomes for a deviating coalition `S` are the
final outcomes of all admissible schedules. -/
noncomputable def game : SwapGame P.D where
  outcomes S := {T | ∃ (C : Finset V) (sch : ℕ → Moves V), (C : Set V) = S ∧
    P.ValidSched C sch ∧ T = P.Final C sch}

end Setting

end AtomicSwap
