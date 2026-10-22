import Podc.Foundations.Combinatorics.HypergraphCover

/-!
# Algorithm MWHVC (Section 3)

Ben-Basat, Even, Kawarabayashi, Schwartzman, *Optimal Distributed Covering Algorithms*, PODC 2019
(arXiv 1902.09377v2).

The input is a hypergraph with edges `inc e ⊆ V` (indexed by a finite type `E`, so parallel edges are
allowed, as in the set-cover reading) and positive vertex weights `w`. The algorithm is a synchronous
primal–dual algorithm on the bipartite vertex/edge network; since every step only uses information of
the vertices of an edge or of the edges of a vertex, we model it by its global-state iteration:
`step` performs one iteration `i ≥ 1` (steps 3a–3f of the paper), `init` is iteration `0`, and
`run I P i` is the state at the end of iteration `i`.

Parameters (`Params`): the rank bound `f`, the approximation parameter `ε`, the multiplier `α`, the
factor `κ` by which the dual variables grow (`κ = 1` in Section 3, `κ = 1/2` in Appendix C), and the
factor `c₀` of the initial deal (`c₀ = 1/2` in Section 3, `c₀ = β` in Appendix B).

State: the cover `C`, the levels `ℓ(v)`, the deals `deal(e)` and the dual variables `δ(e)`.
The set `E'(v)` of uncovered edges at `v` is `uncov I C v`; a vertex is active if `v ∉ C` and
`E'(v) ≠ ∅`; an edge is terminated iff it is covered.

The `while` loop of step 3d is `lvlUp`: the new level is the least `ℓ' ≥ ℓ(v)` with
`∑_{e ∈ E(v)} δ(e) ≤ w(v)(1 - 2^{-(ℓ'+1)})`; every level increment of `v` halves `deal(e)` for every
`e ∈ E'(v)`, so `deal(e)` is multiplied by `2^{-k}` where `k` is the total number of level
increments of the vertices of `e` (`deal1`).
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- An instance of MWHVC: a hypergraph with nonempty edges and positive vertex weights. -/
structure Inst (V E : Type*) where
  /-- The vertices of each hyperedge. -/
  inc : E → Finset V
  /-- The vertex weights. -/
  w : V → ℝ
  inc_nonempty : ∀ e, (inc e).Nonempty
  w_pos : ∀ v, 0 < w v

/-- The parameters of the algorithm. -/
structure Params where
  /-- Upper bound on the rank of the hypergraph (the paper's `f`). -/
  f : ℕ
  /-- Approximation parameter. -/
  ε : ℝ
  /-- Multiplier of the deals. -/
  α : ℝ
  /-- Dual variables grow by `κ · deal(e)` (`κ = 1`: Section 3; `κ = 1/2`: Appendix C). -/
  κ : ℝ
  /-- Initial deal factor (`c₀ = 1/2`: Section 3; `c₀ = β`: Appendix B). -/
  c₀ : ℝ

/-- The paper's assumptions on the parameters (`α ≥ 2` in the paper; `α > 1` suffices). -/
structure Params.Valid (P : Params) (I : Inst V E) : Prop where
  f_pos : 0 < P.f
  rank_le : ∀ e, (I.inc e).card ≤ P.f
  ε_pos : 0 < P.ε
  one_lt_α : 1 < P.α
  κ_pos : 0 < P.κ
  κ_le : P.κ ≤ 1
  c₀_pos : 0 < P.c₀
  c₀_le : P.c₀ ≤ 1 / 2

/-- `β = ε / (f + ε)`. -/
noncomputable def Params.β (P : Params) : ℝ := P.ε / (P.f + P.ε)

/-- `z = ⌈log₂ (1/β)⌉`. -/
noncomputable def Params.z (P : Params) : ℕ := ⌈Real.logb 2 P.β⁻¹⌉₊

/-- The state at the end of an iteration. -/
structure State (V E : Type*) where
  /-- The cover built so far. -/
  C : Finset V
  /-- The levels `ℓ(v)`. -/
  level : V → ℕ
  /-- The deals `deal(e)`. -/
  deal : E → ℝ
  /-- The dual variables `δ(e)`. -/
  δ : E → ℝ

namespace Inst

variable (I : Inst V E)

/-- `E(v)`: the edges containing `v`. -/
abbrev E_ (v : V) : Finset E := edgesAt I.inc v

/-- `|E(v)|`. -/
abbrev deg (v : V) : ℕ := (I.E_ v).card

/-- `∑_{e ∈ E(v)} δ(e)`. -/
abbrev load (δ : E → ℝ) (v : V) : ℝ := Cslib.Hypergraph.load I.inc δ v

/-- The edge `e` is covered by `C`. -/
def Covered (C : Finset V) (e : E) : Prop := ∃ v ∈ I.inc e, v ∈ C

instance (C : Finset V) : DecidablePred (I.Covered C) := fun _ => by
  unfold Covered; infer_instance

/-- `E'(v)`: the uncovered edges containing `v`. -/
def uncov (C : Finset V) (v : V) : Finset E := (I.E_ v).filter fun e => ¬ I.Covered C e

/-- `v` is active (has not terminated): `v ∉ C` and `E'(v) ≠ ∅`. -/
def Active (C : Finset V) (v : V) : Prop := v ∉ C ∧ (I.uncov C v).Nonempty

end Inst

open Classical in
/-- Step 3d (the `while` loop): the least level `ℓ' ≥ ℓ` with `s ≤ w (1 - 2^{-(ℓ'+1)})`. If there is
none (which never happens for active vertices, see `lvlUp_spec`), the level is unchanged. -/
noncomputable def lvlUp (ℓ : ℕ) (s w : ℝ) : ℕ :=
  if h : ∃ k : ℕ, s ≤ w * (1 - (1 / 2 : ℝ) ^ (ℓ + k + 1)) then ℓ + Nat.find h else ℓ

variable (I : Inst V E) (P : Params)

/-- Initial deals (iteration 0): `deal₀(e) = c₀ · min_{v ∈ e} w(v)/|E(v)|`. -/
noncomputable def deal0 (e : E) : ℝ :=
  P.c₀ * (I.inc e).inf' (I.inc_nonempty e) fun v => I.w v / I.deg v

/-- The state at the end of iteration 0. -/
noncomputable def init : State V E where
  C := ∅
  level := fun _ => 0
  deal := deal0 I P
  δ := deal0 I P

open Classical in
/-- Step 3a: `v ∉ C` joins `C` if `∑_{e ∈ E(v)} δ(e) ≥ (1 - β) w(v)`. -/
noncomputable def joinC (s : State V E) : Finset V :=
  s.C ∪ univ.filter fun v => v ∉ s.C ∧ (1 - P.β) * I.w v ≤ I.load s.δ v

open Classical in
/-- Step 3d: new levels of the active vertices. -/
noncomputable def lvl1 (s : State V E) (v : V) : ℕ :=
  if I.Active (joinC I P s) v then lvlUp (s.level v) (I.load s.δ v) (I.w v) else s.level v

open Classical in
/-- Step 3d: every level increment of a vertex of `e` halves `deal(e)` (for uncovered `e`). -/
noncomputable def deal1 (s : State V E) (e : E) : ℝ :=
  if I.Covered (joinC I P s) e then s.deal e
  else s.deal e * (1 / 2 : ℝ) ^ (∑ v ∈ I.inc e, (lvl1 I P s v - s.level v))

/-- Step 3e: the active vertex `v` sends "raise" iff
`∑_{e ∈ E'(v)} deal(e) ≤ α⁻¹ · 2^{-(ℓ(v)+1)} · w(v)` (otherwise it sends "stuck"). -/
def Raise (s : State V E) (v : V) : Prop :=
  ∑ e ∈ I.uncov (joinC I P s) v, deal1 I P s e ≤ P.α⁻¹ * (1 / 2 : ℝ) ^ (lvl1 I P s v + 1) * I.w v

/-- Step 3f: the uncovered edge `e` multiplies its deal by `α` iff all its vertices sent "raise". -/
def RaiseEdge (s : State V E) (e : E) : Prop :=
  ¬ I.Covered (joinC I P s) e ∧ ∀ v ∈ I.inc e, Raise I P s v

open Classical in
/-- Step 3f: the deal after the possible multiplication by `α`. -/
noncomputable def deal2 (s : State V E) (e : E) : ℝ :=
  if RaiseEdge I P s e then P.α * deal1 I P s e else deal1 I P s e

open Classical in
/-- One iteration `i ≥ 1` of Algorithm MWHVC (steps 3a–3f). Covered edges are terminated: their
dual variables are frozen. -/
noncomputable def step (s : State V E) : State V E where
  C := joinC I P s
  level := lvl1 I P s
  deal := deal2 I P s
  δ := fun e => if I.Covered (joinC I P s) e then s.δ e else s.δ e + P.κ * deal2 I P s e

/-- The state at the end of iteration `i`. -/
noncomputable def run : ℕ → State V E
  | 0 => init I P
  | i + 1 => step I P (run i)

/-- The algorithm has terminated at the end of iteration `i`: every edge is covered (hence every
edge and every vertex has terminated). -/
def Terminated (i : ℕ) : Prop := ∀ e, I.Covered (run I P i).C e

/-- Definition 4.5: iteration `i ≥ 1` is an `e`-raise iteration. -/
def RaiseIter (e : E) (i : ℕ) : Prop := 1 ≤ i ∧ RaiseEdge I P (run I P (i - 1)) e

/-- Definition 4.5: iteration `i ≥ 1` is a `v`-stuck iteration: `v` is active in iteration `i`
(after steps 3a–3c) and sends "stuck". -/
def StuckIter (v : V) (i : ℕ) : Prop :=
  1 ≤ i ∧ I.Active (run I P i).C v ∧ ¬ Raise I P (run I P (i - 1)) v

end Podc.CoveringPrimalDual
