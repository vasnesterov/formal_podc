import Cslib.Computability.Distributed.ApproxConsensus.DigraphConditions
import Podc.Foundations.Combinatorics.Digraph.Walk
import Mathlib

/-!
# Crash-tolerant node connectivity and the fault-tolerant diameter

Graph-theoretic notions of Tseng–Vaidya, *Fault-Tolerant (Crash-Tolerant) Consensus in Directed
Graphs* (PODC 2015), Section 2.

We use the shared reach sets of `Cslib/Computability/Distributed/ApproxConsensus/DigraphConditions.lean`:
`Reaches G F a b` says that `a ∉ F` and `b` is reachable from `a` in the reduced graph `G_F`
(Definition 1: the subgraph induced by `V − F`; `Digraph.ReachableAvoiding`).

* `CTConn G k` — Definition 2 (*`k` crash-tolerant node connectivity*): every reduced graph
  `G_F` with `|F| ≤ k` has a node (a *source* / root, Definitions 3–4) reaching all its nodes.
* `ctConn_iff_oneReach` — this is the *1-reach* condition of later work by the same authors
  (every two nodes of `G_F` have a common ancestor in `G_F`). The proof of Theorem 1 uses this
  reformulation implicitly ("there is a pair `i, j` such that no node has paths to both").
* `ReachesWithin G F k a b` — `b` is reachable from `a` in `G_F` by a path with at most `k` edges
  (`a ∉ F` and a walk of length `≤ k` in `G.deleteVerts F`, CSLib's `Relation.RelatesWithinSteps`).
* `FTDiamLE G f D` — `D` bounds the *fault-tolerant diameter* `d` of equation (1): every source
  `s` of every reduced graph `G_F` (`|F| ≤ f`) reaches all of `G_F` within `D` hops, i.e.
  `height(s, G_F) ≤ D`. `ftDiam G f` is the paper's `d` (the least such `D`), and
  `ftDiamLE_card`: `d ≤ n − 1`.
-/

open Finset Relation

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus

variable {V : Type*} [DecidableEq V] {G : Digraph V}

/-- **Definition 2** (crash-tolerant node connectivity): for every `F` with `|F| ≤ k` and
`F ≠ V`, there is a single node `s ∉ F` that has paths to all the nodes of the reduced graph
`G_F`. -/
def CTConn (G : Digraph V) (k : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ k → (∃ v, v ∉ F) → ∃ s, s ∉ F ∧ ∀ v, v ∉ F → Reaches G F s v

/-- `s` is a source (root) of the reduced graph `G_F` (Definition 4): `s ∉ F` and `s` reaches every
node of `G_F` (the shared `Digraph.IsRootAvoiding`; a node of `G_F` with an edge into a root is a
root, `Digraph.IsRootAvoiding.of_adj`). -/
abbrev IsRoot (G : Digraph V) (F : Finset V) (s : V) : Prop := G.IsRootAvoiding ↑F s

/-- Crash-tolerant node connectivity is the *1-reach* condition. -/
theorem ctConn_iff_oneReach [Fintype V] {k : ℕ} : CTConn G k ↔ OneReach G k := by
  classical
  constructor
  · intro h F u v hF hu hv
    obtain ⟨s, -, hs⟩ := h F hF ⟨u, hu⟩
    exact ⟨s, hs v hv, hs u hu⟩
  · intro h F hF hne
    exact Digraph.exists_isRootAvoiding (X := ↑F) hne fun u v hu hv =>
      (h F u v hF hu hv).imp fun _ hw => ⟨hw.2, hw.1⟩

/-! ## Bounded reachability -/

/-- `ReachesWithin G X k a b`: there is a path from `a` to `b` with at most `k` edges in the
subgraph induced by `V − X`. -/
abbrev ReachesWithin (G : Digraph V) (X : Finset V) (k : ℕ) (a b : V) : Prop :=
  a ∉ X ∧ Relation.RelatesWithinSteps (G.deleteVerts ↑X).Adj a b k

/-- Bounded reachability implies reachability. -/
theorem ReachesWithin.reaches {X : Finset V} {k : ℕ} {a b : V} (h : ReachesWithin G X k a b) :
    Reaches G X a b :=
  ⟨h.1, h.2.reflTransGen⟩

/-- The two introduction rules of bounded reachability (`k` hops, avoiding `X`): staying put. -/
theorem ReachesWithin.refl {X : Finset V} (k : ℕ) {a : V} (h : a ∉ X) : ReachesWithin G X k a a :=
  ⟨h, Relation.RelatesWithinSteps.mono k.zero_le (.refl a)⟩

/-- The two introduction rules of bounded reachability: one more arc into `V − X`. -/
theorem ReachesWithin.tail {X : Finset V} {k : ℕ} {a b c : V} (h : ReachesWithin G X k a b)
    (e : G.Adj b c) (hc : c ∉ X) : ReachesWithin G X (k + 1) a c :=
  ⟨h.1, h.2.tail ⟨e, h.reaches.notMem_right, hc⟩⟩

/-- Recursive description: `ReachesWithin` is the least relation closed under `refl` and `tail`
(bridge to the inductive definition `refl | tail`). -/
theorem reachesWithin_succ_iff {X : Finset V} {k : ℕ} {a c : V} :
    ReachesWithin G X (k + 1) a c ↔
      ReachesWithin G X k a c ∨ ∃ b, ReachesWithin G X k a b ∧ G.Adj b c ∧ c ∉ X := by
  constructor
  · rintro ⟨ha, h⟩
    rcases Relation.relatesWithinSteps_succ_iff.1 h with h | ⟨b, hb, e⟩
    · exact .inl ⟨ha, h⟩
    · exact .inr ⟨b, ⟨ha, hb⟩, e.1, e.2.2⟩
  · rintro (h | ⟨b, hb, e, hc⟩)
    · exact ⟨h.1, Relation.RelatesWithinSteps.mono k.le_succ h.2⟩
    · exact hb.tail e hc

/-- `ReachesWithin` in `0` hops: staying at a node outside `X`. -/
theorem reachesWithin_zero_iff {X : Finset V} {a b : V} :
    ReachesWithin G X 0 a b ↔ a ∉ X ∧ a = b := by
  simp [ReachesWithin]

/-- Every reachable node is reachable within `n − 1` hops. -/
theorem reachesWithin_of_reaches [Fintype V] {X : Finset V} {a b : V} (h : Reaches G X a b) :
    ReachesWithin G X (Fintype.card V - 1) a b :=
  ⟨h.1, Digraph.Reachable.relatesWithinSteps h.2⟩

/-! ## The fault-tolerant diameter -/

/-- `D` bounds the fault-tolerant diameter (equation (1)): for every `F` with `|F| ≤ f`, every
root `s` of `G_F` reaches every node of `G_F` by a path of length at most `D`
(i.e. `height(s, G_F) ≤ D`). -/
def FTDiamLE (G : Digraph V) (f D : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ f → ∀ s, IsRoot G F s → ∀ v, v ∉ F → ReachesWithin G F D s v

theorem FTDiamLE.mono {f D D' : ℕ} (h : FTDiamLE G f D) (hD : D ≤ D') : FTDiamLE G f D' :=
  fun F hF s hs v hv => ⟨(h F hF s hs v hv).1, Relation.RelatesWithinSteps.mono hD (h F hF s hs v hv).2⟩

/-- `d ≤ n − 1`. -/
theorem ftDiamLE_card [Fintype V] (f : ℕ) : FTDiamLE G f (Fintype.card V - 1) :=
  fun _ _ _ hs v hv => reachesWithin_of_reaches (hs.2 v hv)

open Classical in
/-- The fault-tolerant diameter `d` of equation (1): the least `D` with `FTDiamLE G f D`
(`max_{|F| ≤ f} max_{roots s of G_F} height(s, G_F)`). -/
noncomputable def ftDiam [Fintype V] (G : Digraph V) (f : ℕ) : ℕ :=
  Nat.find (⟨_, ftDiamLE_card f⟩ : ∃ D, FTDiamLE G f D)

theorem ftDiamLE_ftDiam [Fintype V] (f : ℕ) : FTDiamLE G f (ftDiam G f) := by
  classical exact Nat.find_spec (⟨_, ftDiamLE_card f⟩ : ∃ D, FTDiamLE G f D)

theorem ftDiam_le [Fintype V] {f D : ℕ} (h : FTDiamLE G f D) : ftDiam G f ≤ D := by
  classical exact Nat.find_min' (⟨_, ftDiamLE_card f⟩ : ∃ D, FTDiamLE G f D) h

theorem ftDiam_le_card [Fintype V] (f : ℕ) : ftDiam G f ≤ Fintype.card V - 1 :=
  ftDiam_le (ftDiamLE_card f)

end CrashConsensusDigraph
