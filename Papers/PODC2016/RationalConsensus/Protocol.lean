import Papers.PODC2016.RationalConsensus.Records

/-!
# The strategy `σ_cons` (Section 3.2.2, Algorithm 1 of Halpern–Vilaça)

Agents `Fin n`; at most `f` crashes; the protocol runs `f + 1` rounds.

**Randomness.** Agent `i`'s seed (`Seed n f p`) consists, for every `t ∈ {0, …, f}`, of the secret
`x_i[t] ∈ {0, …, n - t - 1}` and the slope `a_i[t] ∈ 𝔽_p` of the degree-1 polynomial
`q_i^t(X) = x_i[t] + a_i[t] X` over `𝔽_p = ZMod p` (the paper leaves the field unspecified; we take a
prime `p > n`). Agent `j`'s share of `q_i^t` is its value at the evaluation point `j + 1`
(`evalPt`); the paper evaluates at `j` with identifiers `0, …, n - 1`, which hands agent `0` the
secret itself (`q_i^t(0) = x_i[t]`).

**Messages** (`Msg`). In every round `m ≤ f + 1` agent `i` sends to every `j` its status report
(here: for every agent the earliest round in which `i` knows it crashed, `recTab`); in round 1 also
its preference and `j`'s shares; in round `f + 1` also, for every `l ≠ j`, the share of `q_l`
that `i` received from `l` in round 1. The flag `selfShare` adds, in round `f + 1`, `i`'s own share
`q_i(i + 1)`. `selfShare = true` is line 20 of Algorithm 1 as written (`(y_li)_{l ≠ j}` ranges over
`l = i` too; line 14 forgets to define `y_ii`); `selfShare = false` is the prose reading "the
shares it received in round 1", under which Theorem 2 fails for `n = f + 2` and `f = 0`.

**Decision** (`decideVal`, lines 46–56) at the end of round `f + 1`: compute `NC_m` from the
records, the first round `m` that seems clean, `t = n - |NC_m|`, reconstruct `x_l[t]` for
`l ∈ NC_m` by interpolating `l`'s share received in round 1 with one forwarded share, and decide
the preference of the agent with the `(S + 1)`-st highest identifier in `NC_m`, where
`S = Σ_{l ∈ NC_m} x_l[t] mod (n - t)`. Whenever something needed is missing, decide `⊥` (`none`).

**Not modelled** (they never fire when nobody deviates, which is all Theorem 2 is about): the
random "signatures" `z`, the reporter identities in status reports and the consistency checks 1–3
and 5–7 of the paper; check 4 is only kept as "a second share point exists", and check 8 only as
`t ≤ f`. See `differencies.md`.
-/

namespace Podc.RationalConsensus.Cons

open Cslib Cslib.SyncCrash Classical

/-- A seed: for each `t ≤ f`, the secret `x[t] ∈ Fin (n - t)` and the slope of `q^t`. -/
abbrev Seed (n f p : ℕ) : Type := (t : Fin (f + 1)) → Fin (n - t) × ZMod p

instance (n f p : ℕ) [NeZero p] : Fintype (Seed n f p) := inferInstanceAs (Fintype ((t : _) → _))
instance (n f p : ℕ) : DecidableEq (Seed n f p) := inferInstanceAs (DecidableEq ((t : _) → _))
instance (n f p : ℕ) : MeasurableSpace (Seed n f p) := ⊤
instance (n f p : ℕ) [Fact (f < n)] : Nonempty (Seed n f p) :=
  ⟨fun t => (⟨0, by have := (Fact.out : f < n); have := t.2; omega⟩, 0)⟩
instance (n f p : ℕ) : MeasurableSingletonClass (Seed n f p) := ⟨fun _ => trivial⟩

/-- Messages of `σ_cons`. -/
structure Msg (n f p : ℕ) where
  /-- Status report: earliest known crash round of every agent (`⊤`: not known to have crashed). -/
  sr : Fin n → ℕ∞
  /-- The sender's preference (round 1). -/
  pref : Option Bool
  /-- The receiver's shares of the sender's polynomials (round 1). -/
  share : Option (Fin (f + 1) → ZMod p)
  /-- Forwarded shares (round `f + 1`): `fwd l` = the sender's shares of `l`'s polynomials. -/
  fwd : Fin n → Option (Fin (f + 1) → ZMod p)

variable {n f p : ℕ}

/-- Evaluation point of agent `j`. -/
def evalPt (j : Fin n) : ZMod p := ((j : ℕ) + 1 : ℕ)

/-- The shares `q^t(j + 1)`, `t ≤ f`, of the polynomials of a seed. -/
def shareOf (ω : Seed n f p) (j : Fin n) : Fin (f + 1) → ZMod p :=
  fun t => (((ω t).1 : ℕ) : ZMod p) + (ω t).2 * evalPt j

/-- The value at `0` of the line through `(α₁, y₁)` and `(α₂, y₂)`. -/
def interp (α₁ y₁ α₂ y₂ : ZMod p) : ZMod p := y₁ - (y₁ - y₂) * (α₁ - α₂)⁻¹ * α₁

/-- Local histories. -/
abbrev Hist (n f p : ℕ) := Cslib.Byzantine.LockStep.History (Fin n) (Msg n f p)

/-- The crash records of `me` after `t` rounds of history `h` (status reports `SR`, with the
minimum taken over all reports, lines 23–37). -/
noncomputable def recTab (me : Fin n) (h : Hist n f p) : ℕ → Fin n → ℕ∞
  | 0 => fun _ => ⊤
  | t + 1 => fun l =>
    if l = me then ⊤ else
      min (recTab me h t l)
        (min (if rcv h t l = none then ((t + 1 : ℕ) : ℕ∞) else ⊤)
          (Finset.univ.inf fun y => ((rcv h t y).map fun m => m.sr l).getD ⊤))

/-- The message `me` (with input `x`) sends to `q` after history `h`. -/
noncomputable def send (selfShare : Bool) (me : Fin n) (x : Bool × Seed n f p) (h : Hist n f p)
    (q : Fin n) : Option (Msg n f p) :=
  if h.length ≤ f then some
    { sr := recTab me h h.length
      pref := if h.length = 0 then some x.1 else none
      share := if h.length = 0 then some (shareOf x.2 q) else none
      fwd := fun l =>
        if h.length = f ∧ l ≠ q then
          (if l = me then (if selfShare then some (shareOf x.2 me) else none)
           else (rcv h 0 l).bind Msg.share)
        else none }
  else none

/-- The preference of `l` as known to `me`. -/
noncomputable def prefOf (me : Fin n) (v : Bool) (h : Hist n f p) (l : Fin n) : Option Bool :=
  if l = me then some v else (rcv h 0 l).bind Msg.pref

/-- The shares of `l`'s polynomials forwarded to `me` by `y` in round `f + 1`. -/
noncomputable def fwdFrom (me : Fin n) (h : Hist n f p) (l y : Fin n) :
    Option (Fin (f + 1) → ZMod p) :=
  if y = me then none else (rcv h f y).bind fun m => m.fwd l

/-- `me`'s reconstruction of the secret `x_l[t]`: interpolate `l`'s share received in round 1
with the share forwarded by the least agent that forwarded one. -/
noncomputable def secret (me : Fin n) (ω : Seed n f p) (h : Hist n f p) (t : Fin (f + 1))
    (l : Fin n) : Option ℕ :=
  if l = me then some ((ω t).1 : ℕ) else
    let Y := Finset.univ.filter fun y => (fwdFrom me h l y).isSome
    if hY : Y.Nonempty then
      match (rcv h 0 l).bind Msg.share, fwdFrom me h l (Y.min' hY) with
      | some s₁, some s₂ => some (interp (evalPt me) (s₁ t) (evalPt (Y.min' hY)) (s₂ t)).val
      | _, _ => none
    else none

/-- The decision of `me` at the end of round `f + 1` (`none` = `⊥`). -/
noncomputable def decideVal (me : Fin n) (x : Bool × Seed n f p) (h : Hist n f p) :
    Option Bool :=
  let R := recTab me h (f + 1)
  match firstClean f R with
  | none => none
  | some m =>
    let S := NC R m
    if ht : n - S.card ≤ f then
      let t : Fin (f + 1) := ⟨n - S.card, by omega⟩
      if ∀ l ∈ S, (prefOf me x.1 h l).isSome ∧ (secret me x.2 h t l).isSome then
        let sum := (∑ l ∈ S, (secret me x.2 h t l).getD 0) % (n - (n - S.card))
        ((S.sort (· ≤ ·)).reverse[sum]?).bind (prefOf me x.1 h)
      else none
    else none

/-- **The strategy profile `σ_cons`** (`selfShare = true`: Algorithm 1 as written; `false`: the
received-only reading of the forwarding step). -/
noncomputable def sigmaCons (selfShare : Bool) : Profile (Fin n) (Msg n f p) (Seed n f p) where
  send := send selfShare
  decide me x h := if h.length = f + 1 then some (decideVal me x h) else none

/-- Independent uniform seeds (the uniform distribution on `Fin n → Seed n f p`). -/
noncomputable def seedMeasure (n f p : ℕ) [NeZero p] [Fact (f < n)] : MeasureTheory.Measure (Fin n → Seed n f p) :=
  (PMF.uniformOfFintype (Fin n → Seed n f p)).toMeasure

end Podc.RationalConsensus.Cons
