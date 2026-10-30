import Papers.PODC2021.SoreLoserHedging.Premiums

/-!
# The hedged multi-party swap (§7) as a timed execution model

**Time** is discrete, in units of `Δ`; the protocol starts at time `0`. Conforming parties act in
lock-step: a reaction to an event that is on chain at time `t` takes effect at time `t + 1`.
Deadlines are inclusive.

**Timeouts.** The paper only says that "each step takes time at most `Δ`" and that "each
following step's timeout increases by `Δ`", and refers to [Herlihy 2018] for the base protocol.
We fix a consistent family (`Swap`): escrow premiums on arcs leaving `v` must be deposited by
`dl1 v`; redemption premiums with path `q` by `t1 + |q|` (here `|q|` is the number of vertices
of `q`); activation is checked at `t2`; assets on arcs leaving `v` must be escrowed by `dl3 v`;
a hashkey with path `q`, and a redemption premium with path `q`, time out at `B + |q|`.
The constraints (`dl1_*`, `t2_ge`, `dl3_*`) give every conforming party one `Δ` of slack per
step, as in the paper.

**Executions** are records (`Exec`) of the on-chain events: escrow premiums `ep u v`, redemption
premiums `rp i u v` (for the hashkey of leader `i`, deposited by `v` on `(u, v)`, with their
path), escrowed assets `es u v`, and the first accepted hashkey `ky i u v` for leader `i` on
`(u, v)` (presented by `v`, with its path). `fp i v` / `fk i v` are the first redemption premium
/ hashkey for `i` that `v` observes on a leaving arc (ties broken by the scheduler).

`Admissible S C X` says that `X` is an execution of the hedged protocol in which the parties
outside the coalition `C` conform:
* **contract rules** (everybody): deadlines, well-formed paths (a redemption premium path is a
  simple path from the depositor to the leader; a hashkey path is a path in the sense of
  [Herlihy 2018]: all vertices but the last distinct);
* **unforgeability**: a path containing a conforming party `x` (not at the head) has, from `x` on,
  exactly the path that `x` itself signed, no later than the event (premiums and keys are public
  as soon as they are submitted; front-running is allowed);
* **conforming behaviour**, phase by phase as in §7.1, including the truncated phases that the
  proofs of Lemmas 3–5 describe: a follower deposits escrow premiums only after all entering
  arcs carry one; a leader deposits its redemption premiums only if all entering escrow premiums
  arrived; parties escrow assets only on *activated* arcs; a leader that escrowed nothing
  releases its secret at once (Lemma 4's proof); otherwise it releases it iff all entering arcs
  carry assets (Lemma 3's proof).

The coalition is arbitrary otherwise: it may deposit, escrow, or present keys whenever the
contracts accept them.

**Payoffs.** An activated escrow premium `E(u, v)` goes to `v` if the asset on `(u, v)` is not
escrowed in time (else it is refunded). A redemption premium `Rᵢ(q, u)` on `(u, v)` goes to `u`
unless `v` presents a hashkey for `i` on `(u, v)` by `B + |q|`. `net v` is the net premium
profit of `v`.
-/

namespace Podc.SoreLoserHedging

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A hedged multi-party swap: digraph, leaders (a feedback vertex set), premium unit `p`, and
consistent timeouts. -/
structure Swap (V : Type*) [Fintype V] [DecidableEq V] where
  /-- the swap digraph -/
  G : Digraph V
  [dec : DecidableRel G.Adj]
  /-- no self-loops (nobody transfers an asset to itself) -/
  loopless : ∀ v, ¬ G.Adj v v
  /-- the leaders -/
  L : Finset V
  /-- the leaders form a feedback vertex set -/
  fvs : IsFVS G L
  /-- the premium per asset -/
  p : ℕ
  /-- deadline for escrow premiums on arcs leaving `v` -/
  dl1 : V → ℕ
  /-- end of the escrow-premium phase; leaders deposit redemption premiums at `t1 + 1` -/
  t1 : ℕ
  /-- activation deadline (end of the redemption-premium phase) -/
  t2 : ℕ
  /-- deadline for escrowing assets on arcs leaving `v` -/
  dl3 : V → ℕ
  /-- hashkeys and redemption premiums with path `q` time out at `B + |q|` -/
  B : ℕ
  dl1_le : ∀ v, dl1 v ≤ t1
  t2_ge : t1 + Fintype.card V ≤ t2
  dl3_ge : ∀ v, t2 + 1 ≤ dl3 v
  dl3_fol : ∀ u v, G.Adj u v → v ∉ L → dl3 u + 1 ≤ dl3 v
  dl3_le : ∀ v, dl3 v ≤ B

attribute [instance] Swap.dec

/-- A redemption-premium path for leader `i` deposited by `v`: a simple path from `v` to `i`. -/
def PPath (G : Digraph V) (i v : V) (q : List V) : Prop :=
  q.head? = some v ∧ q.getLast? = some i ∧ q.IsChain G.Adj ∧ q.Nodup

/-- A hashkey path for leader `i` presented by `v` (paths of [Herlihy 2018]: all vertices except
possibly the last are distinct). -/
def KPath (G : Digraph V) (i v : V) (q : List V) : Prop :=
  q.head? = some v ∧ q.getLast? = some i ∧ q.IsChain G.Adj ∧ q.dropLast.Nodup

instance (G : Digraph V) [DecidableRel G.Adj] (i v : V) : DecidablePred (PPath G i v) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (G : Digraph V) [DecidableRel G.Adj] (i v : V) : DecidablePred (KPath G i v) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The on-chain events of an execution. -/
structure Exec (V : Type*) where
  /-- escrow premium on `(u, v)` (deposited by `u`): time -/
  ep : V → V → Option ℕ
  /-- `rp i u v`: redemption premium for leader `i`'s hashkey on `(u, v)` (deposited by `v`):
  time and path -/
  rp : V → V → V → Option (ℕ × List V)
  /-- asset escrowed on `(u, v)` (by `u`): time -/
  es : V → V → Option ℕ
  /-- `ky i u v`: first accepted hashkey for leader `i` on `(u, v)` (presented by `v`): time and
  path -/
  ky : V → V → V → Option (ℕ × List V)
  /-- `fp i v`: first redemption premium for `i` observed by `v` on a leaving arc -/
  fp : V → V → Option (ℕ × List V)
  /-- `fk i v`: first hashkey for `i` observed by `v` on a leaving arc -/
  fk : V → V → Option (ℕ × List V)

/-- An optional timed event happened no later than `d`. -/
def OptLe {α : Type*} : Option (ℕ × α) → ℕ → Prop
  | some (t, _), d => t ≤ d
  | none, _ => False

instance {α : Type*} (o : Option (ℕ × α)) (d : ℕ) : Decidable (OptLe o d) := by
  cases o with
  | none => exact isFalse id
  | some a => exact inferInstanceAs (Decidable (a.1 ≤ d))

lemma optLe_iff {α : Type*} {o : Option (ℕ × α)} {d : ℕ} :
    OptLe o d ↔ ∃ t a, o = some (t, a) ∧ t ≤ d := by
  cases o with
  | none => simp [OptLe]
  | some a => obtain ⟨t, a⟩ := a; simp [OptLe]

/-- `some t` if `t ≤ d` (an attempt at time `t` against deadline `d`). -/
def acc (t d : ℕ) : Option ℕ := if t ≤ d then some t else none

namespace Swap

variable (S : Swap V) (X : Exec V)

/-- If all arcs entering `v` carry an event of `f`, the time of the last one. -/
def allIn (f : V → V → Option ℕ) (v : V) : Option ℕ :=
  if ∀ u ∈ inN S.G v, (f u v).isSome then some ((inN S.G v).sup fun u => (f u v).getD 0) else none

/-- The escrow premium on `(u, v)` is *activated*: it was deposited, and by `t2` the arc
carries redemption premiums for all leaders' hashkeys. -/
def Act (u v : V) : Prop := (X.ep u v).isSome ∧ ∀ i ∈ S.L, OptLe (X.rp i u v) S.t2

instance (u v : V) : Decidable (S.Act X u v) := inferInstanceAs (Decidable (_ ∧ _))

/-- Time at which a conforming leader `v` releases its secret (calls `unlock` with path `[v]` on
its entering arcs): at `t2 + 1` if it escrowed nothing (no activated leaving arc), otherwise
one step after its entering arcs all carry assets (and not before Phase Three). -/
def rel (v : V) : Option ℕ :=
  if ∀ w ∈ outN S.G v, ¬ S.Act X v w then some (S.t2 + 1)
  else (S.allIn X.es v).map fun m => max m S.t2 + 1

/-- What a conforming `x` has signed on a hashkey path for leader `i`, as of time `t`: the
suffix `q₂` following `x` in a key path is `[]` with the secret released (if `x = i`), or the
path of the first key `x` observed (if `x ≠ i`), and the signature was submitted by time `t`. -/
def Signed (i x : V) (q₂ : List V) (t : ℕ) : Prop :=
  if x = i then q₂ = [] ∧ ∃ r, S.rel X x = some r ∧ r ≤ t
  else ∃ tf, X.fk i x = some (tf, q₂) ∧ tf + 1 ≤ t

/-- `X` is an execution of the hedged protocol in which every party outside `C` conforms. -/
structure Admissible (C : Finset V) : Prop where
  /-- escrow-premium contracts: arc, deadline -/
  ep_ok : ∀ u v t, X.ep u v = some t → S.G.Adj u v ∧ t ≤ S.dl1 u
  /-- redemption-premium contracts: arc, leader, simple path from the depositor, deadline -/
  rp_ok : ∀ i u v t q, X.rp i u v = some (t, q) →
    S.G.Adj u v ∧ i ∈ S.L ∧ PPath S.G i v q ∧ t ≤ S.t1 + q.length
  /-- asset escrow: arc, deadline -/
  es_ok : ∀ u v t, X.es u v = some t → S.G.Adj u v ∧ t ≤ S.dl3 u
  /-- hashlocks: arc, leader, key path from the presenter, deadline `B + |q|` -/
  ky_ok : ∀ i u v t q, X.ky i u v = some (t, q) →
    S.G.Adj u v ∧ i ∈ S.L ∧ KPath S.G i v q ∧ t ≤ S.B + q.length
  /-- unforgeable premium paths -/
  rp_sig : ∀ i u v t q, X.rp i u v = some (t, q) → ∀ k (hk : k < q.length), 0 < k →
    q[k] ∉ C → ∃ u' t', X.rp i u' q[k] = some (t', q.drop k) ∧ t' ≤ t
  /-- unforgeable hashkeys -/
  ky_sig : ∀ i u v t q, X.ky i u v = some (t, q) → ∀ k (hk : k < q.length), 0 < k →
    q[k] ∉ C → S.Signed X i q[k] (q.drop (k + 1)) t
  /-- first observed premium: it is on a leaving arc, and no earlier one exists -/
  fp_some : ∀ i v t q, X.fp i v = some (t, q) →
    (∃ w ∈ outN S.G v, X.rp i v w = some (t, q)) ∧
    ∀ w ∈ outN S.G v, ∀ t' q', X.rp i v w = some (t', q') → t ≤ t'
  fp_none : ∀ i v, X.fp i v = none → ∀ w ∈ outN S.G v, X.rp i v w = none
  /-- first observed hashkey -/
  fk_some : ∀ i v t q, X.fk i v = some (t, q) →
    (∃ w ∈ outN S.G v, X.ky i v w = some (t, q)) ∧
    ∀ w ∈ outN S.G v, ∀ t' q', X.ky i v w = some (t', q') → t ≤ t'
  fk_none : ∀ i v, X.fk i v = none → ∀ w ∈ outN S.G v, X.ky i v w = none
  /-- Phase 1 (escrow premiums): leaders deposit at once; followers once all entering arcs
  carry escrow premiums -/
  conf_ep : ∀ v ∉ C, ∀ w ∈ outN S.G v, X.ep v w =
    if v ∈ S.L then acc 1 (S.dl1 v) else (S.allIn X.ep v).bind fun m => acc (m + 1) (S.dl1 v)
  /-- Phase 2, leader `v`: deposits `Rᵥ(v, u)` on every entering arc at `t1 + 1` iff all
  entering escrow premiums arrived by `t1` -/
  conf_rp_lead : ∀ v ∉ C, v ∈ S.L → ∀ u ∈ inN S.G v, X.rp v u v =
    if ∀ u' ∈ inN S.G v, OptLe ((X.ep u' v).map fun t => (t, ())) S.t1 then
      some (S.t1 + 1, [v]) else none
  /-- Phase 2, other parties: on the first premium `Rᵢ(q, v)` on a leaving arc, deposit
  `Rᵢ(v ∥ q, u)` on every entering arc if `v ∥ q` is a path -/
  conf_rp : ∀ v ∉ C, ∀ i, i ≠ v → ∀ u ∈ inN S.G v, X.rp i u v =
    match X.fp i v with
    | some (t, q) => if v ∉ q then some (t + 1, v :: q) else none
    | none => none
  /-- Phase 3: escrow assets on activated leaving arcs (leaders at once, followers once all
  entering arcs carry assets) -/
  conf_es : ∀ v ∉ C, ∀ w ∈ outN S.G v, X.es v w =
    if S.Act X v w then
      (if v ∈ S.L then acc (S.t2 + 1) (S.dl3 v)
       else (S.allIn X.es v).bind fun m => acc (max m S.t2 + 1) (S.dl3 v))
    else none
  /-- Phase 4, leader: present `[v]` on entering arcs at release time -/
  conf_ky_lead : ∀ v ∉ C, v ∈ S.L → ∀ u ∈ inN S.G v, X.ky v u v =
    (S.rel X v).bind fun r => if r ≤ S.B + 1 then some (r, [v]) else none
  /-- Phase 4, forwarding: on the first hashkey with path `q` on a leaving arc, present `v ∥ q`
  on every entering arc (accepted iff it is a key path within its deadline) -/
  conf_ky : ∀ v ∉ C, ∀ i, i ≠ v → ∀ u ∈ inN S.G v, X.ky i u v =
    match X.fk i v with
    | some (t, q) => if KPath S.G i v (v :: q) ∧ t + 1 ≤ S.B + (v :: q).length then
        some (t + 1, v :: q) else none
    | none => none

/-! ### Payoffs -/

/-- Escrow premium paid by `u` to `v` on `(u, v)`: `E(u, v)` if activated and the asset was not
escrowed in time. -/
noncomputable def flowE (u v : V) : ℕ :=
  if S.Act X u v ∧ X.es u v = none then Ein S.G S.L S.p S.fvs v else 0

/-- Redemption premium for leader `i` paid by `v` to `u` on `(u, v)`: `Rᵢ(q, u)` unless `v`
presented a hashkey for `i` on `(u, v)` by `B + |q|`. -/
def flowR (i u v : V) : ℕ :=
  match X.rp i u v with
  | some (_, q) => if OptLe (X.ky i u v) (S.B + q.length) then 0 else R S.G S.p q u
  | none => 0

/-- `v` is awarded the redemption premium for leader `i` on its leaving arc `(v, w)`: the
premium was deposited and no hashkey for `i` was presented on `(v, w)` in time. -/
def Aw (i v w : V) : Prop :=
  match X.rp i v w with
  | some (_, q) => ¬ OptLe (X.ky i v w) (S.B + q.length)
  | none => False

instance (i v w : V) : Decidable (S.Aw X i v w) := by
  unfold Aw; split <;> infer_instance

/-- The leaving arcs on which `v` is awarded the redemption premium for `i`. -/
def awd (i v : V) : Finset V := (outN S.G v).filter (S.Aw X i v)

/-- Net escrow-premium profit of `v`. -/
noncomputable def netE (v : V) : ℤ :=
  ∑ u ∈ inN S.G v, (S.flowE X u v : ℤ) - ∑ w ∈ outN S.G v, (S.flowE X v w : ℤ)

/-- Net redemption-premium profit of `v` for leader `i`'s hashkey. -/
def netR (i v : V) : ℤ :=
  ∑ w ∈ outN S.G v, (S.flowR X i v w : ℤ) - ∑ u ∈ inN S.G v, (S.flowR X i u v : ℤ)

/-- Net premium profit of `v`. -/
noncomputable def net (v : V) : ℤ := S.netE X v + ∑ i ∈ S.L, S.netR X i v

/-- The asset on `(u, v)` is redeemed: escrowed and unlocked by all leaders' hashkeys. -/
def Redeemed (u v : V) : Prop := (X.es u v).isSome ∧ ∀ i ∈ S.L, (X.ky i u v).isSome

instance (u v : V) : Decidable (S.Redeemed X u v) := inferInstanceAs (Decidable (_ ∧ _))

/-- The assets that `v` escrowed and that were not redeemed. -/
def lost (v : V) : Finset V := (outN S.G v).filter fun w => (X.es v w).isSome ∧ ¬ S.Redeemed X v w

/-- The assets that `v` escrowed. -/
def esc (v : V) : Finset V := (outN S.G v).filter fun w => (X.es v w).isSome

end Swap

end Podc.SoreLoserHedging
