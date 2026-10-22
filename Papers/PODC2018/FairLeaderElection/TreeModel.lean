import Mathlib

/-!
# Asynchronous message passing on a graph, and leader election as a game (Sections 2, 7 of [YM18])

[YM18] A. Yifrach, Y. Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018 (arXiv:1805.04778v2).

**Model** (Section 2, for an arbitrary communication graph). Processors are the vertices of a finite
simple graph `G` on `V` (the ids, known to everybody). Neighbours communicate over reliable FIFO links
(one per direction). Processors are deterministic and event driven; the randomness of processor `v` is
an input `i ∈ I v` drawn uniformly from a finite set, independently of the other processors (the
input space is the product `∀ v, I v`). A processor (`GProc`) is given by

* `sent h w`: all messages sent to `w` after processing the history `h` (the list of received
  `(sender, message)` pairs, in order of reception — the processor sees the interleaving of its
  links); `sent [] w` are the messages sent at wake-up; sending is incremental;
* `out h`: `some o` if after processing `h` it terminates with output `o : Option V` (`none` = `⊥`).

A configuration is the vector of processed histories; a step on the directed link `(u, v)` delivers
the next pending message from `u` to `v` if `u, v` are adjacent and `v` has not terminated
(`gdeliver`). An oblivious schedule is a sequence of directed links `σ : ℕ → V × V` (`grun`), fair if
every directed edge occurs infinitely often (`GFair`). The outcome (`goutcome`) is `some o` if every
processor terminates with output `some o`, otherwise `FAIL = none`.

**Game** (Definitions 2.1–2.3). `prob`, `expU`: probability and expected utility over the uniform
inputs; `IsRational` (Def. 2.1), `Protocol.deviate` (Def. 2.2: the members of a coalition `C` run
arbitrary strategies, which may depend on their own random input), `IsFLE` (every leader has
probability exactly `1/n` for every fair schedule), `IsResilient` (Def. 2.3).
Protocols are general (not necessarily symmetric), as in Appendix F; since a processor knows its id,
this is no restriction.

**Definition 7.1** (`IsKSimTree`). As written, Def. 7.1 asks for a graph homomorphism `f : G → T`
into a tree with connected fibres of size `≤ k`; since a tree has no loops, an edge inside a fibre is
impossible, so all fibres are singletons (`IsKSimTreeLiteral.card_fiber_le_one`) and the definition
does not depend on `k`. The intended notion (stated in words after Def. 7.1 and used in Cor. F.4) is a
partition of `V` into connected parts of size `≤ k` whose quotient graph is (a subgraph of) a tree:
every edge of `G` lies inside a part or joins two parts adjacent in `T`. This is `IsKSimTree`.
-/

namespace Podc.FairLeaderElection.Trees

/-- A deterministic event-driven processor on a graph with vertex set `V`, messages `M` and outputs
`Option V` (`none` is `⊥`). -/
structure GProc (V M : Type*) where
  /-- All messages sent to `w` after processing the history `h`. -/
  sent : List (V × M) → V → List M
  /-- Sending is incremental. -/
  sent_snoc : ∀ h x w, sent h w <+: sent (h ++ [x]) w
  /-- `out h = some o`: having processed `h`, the processor terminates with output `o`. -/
  out : List (V × M) → Option (Option V)

variable {V M : Type*} [DecidableEq V]

/-- Configurations: the history processed by every processor. -/
abbrev GConfig (V M : Type*) := V → List (V × M)

/-- The number of messages `v` has received from `u`. -/
def received (c : GConfig V M) (u v : V) : ℕ := ((c v).filter (fun x => x.1 = u)).length

/-- The messages sent by `u` to `v` and not yet received. -/
def pending (P : V → GProc V M) (c : GConfig V M) (u v : V) : List M :=
  ((P u).sent (c u) v).drop (received c u v)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Deliver the next pending message on the directed link `e = (u, v)` (a no-op if `u, v` are not
adjacent, nothing is pending, or `v` has terminated). -/
def gdeliver (P : V → GProc V M) (c : GConfig V M) (e : V × V) : GConfig V M :=
  if G.Adj e.1 e.2 ∧ (P e.2).out (c e.2) = none then
    Function.update c e.2 (c e.2 ++ ((pending P c e.1 e.2).take 1).map (Prod.mk e.1))
  else c

/-- The execution of the profile `P` under the oblivious schedule `σ`. -/
def grun (P : V → GProc V M) (σ : ℕ → V × V) : ℕ → GConfig V M
  | 0 => fun _ => []
  | t + 1 => gdeliver G P (grun P σ t) (σ t)

/-- A schedule is fair if every directed edge is scheduled infinitely often. -/
def GFair (σ : ℕ → V × V) : Prop := ∀ u v, G.Adj u v → ∀ N, ∃ t, N ≤ t ∧ σ t = (u, v)

/-- The outcome of the execution: `some o` if every processor terminates with output `some o`,
otherwise `FAIL` (`none`). -/
noncomputable def goutcome (P : V → GProc V M) (σ : ℕ → V × V) : Option V :=
  open Classical in
  if h : ∃ o, ∀ v, ∃ t, (P v).out (grun G P σ t v) = some (some o) then some h.choose else none

/-- A protocol: the strategy of every processor as a function of its random input. -/
structure Protocol (V M : Type*) (I : V → Type*) where
  /-- The strategy of `v` with input `i`. -/
  proc : (v : V) → I v → GProc V M

variable {I : V → Type*}

/-- The profile of strategies for the joint input `ω`. -/
def Protocol.profile (P : Protocol V M I) (ω : ∀ v, I v) : V → GProc V M := fun v => P.proc v (ω v)

/-- Definition 2.2: the adversarial deviation of the coalition `C` running the strategies `A`. -/
def Protocol.deviate (P : Protocol V M I) (C : Finset V) (A : (v : V) → I v → GProc V M) :
    Protocol V M I :=
  ⟨fun v i => if v ∈ C then A v i else P.proc v i⟩

variable [Fintype V] [∀ v, Fintype (I v)]

/-- The probability (over uniform independent inputs) that the outcome is `o`. -/
noncomputable def prob (P : Protocol V M I) (σ : ℕ → V × V) (o : Option V) : ℝ :=
  open Classical in
  ((Finset.univ.filter fun ω : (∀ v, I v) => goutcome G (P.profile ω) σ = o).card : ℝ) /
    Fintype.card (∀ v, I v)

/-- The expected utility. -/
noncomputable def expU (P : Protocol V M I) (σ : ℕ → V × V) (u : Option V → ℝ) : ℝ :=
  (∑ ω : (∀ v, I v), u (goutcome G (P.profile ω) σ)) / Fintype.card (∀ v, I v)

/-- Definition 2.1: a rational utility `u : V ∪ {FAIL} → [0, 1]` with `u FAIL = 0`. -/
def IsRational (u : Option V → ℝ) : Prop := u none = 0 ∧ ∀ o, 0 ≤ u o ∧ u o ≤ 1

/-- Fair leader election: for every fair schedule every processor is elected with probability
exactly `1/n`. -/
def IsFLE (P : Protocol V M I) : Prop :=
  ∀ σ, GFair G σ → ∀ j : V, prob G P σ (some j) = 1 / Fintype.card V

/-- Definition 2.3: `P` is `ε`-`k`-resilient if for every fair schedule, all rational utilities,
every coalition of size `k` and every adversarial deviation, some member of the coalition gains at
most `ε`. -/
def IsResilient (P : Protocol V M I) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ σ, GFair G σ → ∀ u : V → Option V → ℝ, (∀ p, IsRational (u p)) →
    ∀ C : Finset V, C.card = k → ∀ A : (v : V) → I v → GProc V M,
      ∃ p ∈ C, expU G (P.deviate C A) σ (u p) ≤ expU G P σ (u p) + ε

/-! ### Definition 7.1 -/

/-- Definition 7.1 **as written**: a graph homomorphism `f : G →g T` into a tree whose fibres have
size `≤ k` and are connected. -/
def IsKSimTreeLiteral (k : ℕ) : Prop :=
  ∃ (W : Type) (T : SimpleGraph W) (f : G →g T), T.IsTree ∧
    (∀ w, (f ⁻¹' {w}).ncard ≤ k) ∧ ∀ w, (G.induce (f ⁻¹' {w})).Connected

/-- Definition 7.1 **as intended**: a partition of `V` (the fibres of `f`) into connected parts of
size `≤ k` such that every edge of `G` lies inside a part or joins two parts adjacent in the tree
`T`. -/
def IsKSimTree (k : ℕ) : Prop :=
  ∃ (W : Type) (T : SimpleGraph W) (f : V → W), T.IsTree ∧
    (∀ w, (f ⁻¹' {w}).ncard ≤ k) ∧ (∀ w, (G.induce (f ⁻¹' {w})).Connected) ∧
    ∀ x y, G.Adj x y → f x = f y ∨ T.Adj (f x) (f y)

omit [DecidableRel G.Adj] in
/-- Definition 7.1 as written is degenerate: all fibres of the homomorphism are singletons (a
connected fibre with two vertices contains an edge, which a homomorphism into a loopless graph cannot
contract). -/
theorem IsKSimTreeLiteral.card_fiber_le_one {k : ℕ} (h : IsKSimTreeLiteral G k) :
    IsKSimTreeLiteral G 1 := by
  obtain ⟨W, T, f, hT, -, hconn⟩ := h
  refine ⟨W, T, f, hT, fun w => ?_, hconn⟩
  rw [Set.ncard_le_one]
  intro x hx y hy
  by_contra hxy
  obtain ⟨p⟩ := (hconn w).preconnected ⟨x, hx⟩ ⟨y, hy⟩
  cases p with
  | nil => exact hxy rfl
  | @cons _ z _ hadj _ =>
    have h1 : G.Adj x z.1 := hadj
    have hfz : f z.1 = w := z.2
    have := f.map_rel h1
    rw [show f x = w from hx, hfz] at this
    exact this.ne rfl

end Podc.FairLeaderElection.Trees
