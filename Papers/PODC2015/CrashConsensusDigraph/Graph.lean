import Papers.PODC2020.AsyncApproxBCDirected.Graph

/-!
# Crash-tolerant node connectivity and the fault-tolerant diameter

Graph-theoretic notions of Tseng–Vaidya, *Fault-Tolerant (Crash-Tolerant) Consensus in Directed
Graphs* (PODC 2015), Section 2.

We reuse the reach sets of `Papers/PODC2020/AsyncApproxBCDirected/Graph.lean`:
`Reaches G F a b` says that `a ∉ F` and `b` is reachable from `a` in the reduced graph `G_F`
(Definition 1: the subgraph induced by `V − F`).

* `CTConn G k` — Definition 2 (*`k` crash-tolerant node connectivity*): every reduced graph
  `G_F` with `|F| ≤ k` has a node (a *source* / root, Definitions 3–4) reaching all its nodes.
* `ctConn_iff_oneReach` — this is the *1-reach* condition of later work by the same authors
  (every two nodes of `G_F` have a common ancestor in `G_F`). The proof of Theorem 1 uses this
  reformulation implicitly ("there is a pair `i, j` such that no node has paths to both").
* `ReachesWithin G F k a b` — `b` is reachable from `a` in `G_F` by a path with at most `k` edges.
* `FTDiamLE G f D` — `D` bounds the *fault-tolerant diameter* `d` of equation (1): every source
  `s` of every reduced graph `G_F` (`|F| ≤ f`) reaches all of `G_F` within `D` hops, i.e.
  `height(s, G_F) ≤ D`. `ftDiam G f` is the paper's `d` (the least such `D`), and
  `ftDiamLE_card`: `d ≤ n − 1`.
-/

open Finset Relation

-- CSLib candidate (directed-network fault-tolerance conditions)

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

variable {V : Type*} [DecidableEq V] {G : Digraph V}

/-- **Definition 2** (crash-tolerant node connectivity): for every `F` with `|F| ≤ k` and
`F ≠ V`, there is a single node `s ∉ F` that has paths to all the nodes of the reduced graph
`G_F`. -/
def CTConn (G : Digraph V) (k : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ k → (∃ v, v ∉ F) → ∃ s, s ∉ F ∧ ∀ v, v ∉ F → Reaches G F s v

/-- `s` is a source (root) of the reduced graph `G_F` (Definition 4). -/
def IsRoot (G : Digraph V) (F : Finset V) (s : V) : Prop := s ∉ F ∧ ∀ v, v ∉ F → Reaches G F s v

/-- A node of `G_F` with an edge into a root is a root (roots form the source component). -/
theorem IsRoot.of_adj {F : Finset V} {u w : V} (hw : IsRoot G F w) (e : G.Adj u w) (hu : u ∉ F) :
    IsRoot G F u :=
  ⟨hu, fun v hv => (hw.2 v hv).head e hu⟩

/-- Crash-tolerant node connectivity is the *1-reach* condition. -/
theorem ctConn_iff_oneReach [Fintype V] {k : ℕ} : CTConn G k ↔ OneReach G k := by
  classical
  constructor
  · intro h F u v hF hu hv
    obtain ⟨s, -, hs⟩ := h F hF ⟨u, hu⟩
    exact ⟨s, hs v hv, hs u hu⟩
  · intro h F hF ⟨v₀, hv₀⟩
    set D : V → Finset V := fun s => univ.filter fun x => Reaches G F s x
    obtain ⟨s, hsF, hmax⟩ := Finset.exists_max_image (univ.filter fun x => x ∉ F)
      (fun s => (D s).card) ⟨v₀, by simp [hv₀]⟩
    simp only [mem_filter, mem_univ, true_and] at hsF hmax
    refine ⟨s, hsF, fun v hv => ?_⟩
    by_contra hsv
    obtain ⟨w, hws, hwv⟩ := h F v s hF hv hsF
    have hsub : D s ⊂ D w := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨v, by simp [D, hwv], by simp [D, hsv]⟩
      · intro x hx
        simp only [D, mem_filter, mem_univ, true_and] at hx ⊢
        exact hws.trans hx
    have := hmax w hws.1
    have := Finset.card_lt_card hsub
    omega

/-! ## Bounded reachability -/

/-- `ReachesWithin G X k a b`: there is a path from `a` to `b` with at most `k` edges in the
subgraph induced by `V − X`. -/
inductive ReachesWithin (G : Digraph V) (X : Finset V) : ℕ → V → V → Prop
  | refl {a : V} (k : ℕ) : a ∉ X → ReachesWithin G X k a a
  | tail {k : ℕ} {a b c : V} : ReachesWithin G X k a b → G.Adj b c → c ∉ X →
      ReachesWithin G X (k + 1) a c

namespace ReachesWithin

variable {X : Finset V}

theorem notMem_right {k : ℕ} {a b : V} (h : ReachesWithin G X k a b) : b ∉ X := by
  cases h with
  | refl _ h => exact h
  | tail _ _ h => exact h

theorem notMem_left {k : ℕ} {a b : V} (h : ReachesWithin G X k a b) : a ∉ X := by
  induction h with
  | refl _ h => exact h
  | tail _ _ _ ih => exact ih

theorem succ {k : ℕ} {a b : V} (h : ReachesWithin G X k a b) : ReachesWithin G X (k + 1) a b := by
  induction h with
  | refl k h => exact .refl _ h
  | tail _ e hc ih => exact .tail ih e hc

theorem mono {k k' : ℕ} {a b : V} (h : ReachesWithin G X k a b) (hk : k ≤ k') :
    ReachesWithin G X k' a b := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

theorem head {k : ℕ} {a b c : V} (e : G.Adj a b) (ha : a ∉ X) (h : ReachesWithin G X k b c) :
    ReachesWithin G X (k + 1) a c := by
  induction h with
  | refl k hb => exact (ReachesWithin.tail (.refl 0 ha) e hb).mono (by omega)
  | tail _ e' hc ih => exact .tail (ih e) e' hc

theorem zero_eq {a b : V} (h : ReachesWithin G X 0 a b) : a = b := by
  cases h with
  | refl => rfl

theorem reaches {k : ℕ} {a b : V} (h : ReachesWithin G X k a b) : Reaches G X a b := by
  induction h with
  | refl _ h => exact Reaches.refl h
  | tail _ e hc ih => exact ih.tail e hc

end ReachesWithin

/-- A node list forming a chain of `G` inside `V − X` gives bounded reachability. -/
theorem reachesWithin_of_chain {X : Finset V} :
    ∀ (p : List V) (a b : V), p.head? = some a → p.getLast? = some b → p.IsChain G.Adj →
      (∀ y ∈ p, y ∉ X) → ReachesWithin G X (p.length - 1) a b
  | [], _, _, h, _, _, _ => by simp at h
  | [x], a, b, ha, hb, _, hX => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at ha hb
    subst ha hb
    exact .refl _ (hX _ (by simp))
  | x :: y :: q, a, b, ha, hb, hc, hX => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.isChain_cons_cons] at hc
    have ih := reachesWithin_of_chain (y :: q) y b rfl (by simpa using hb) hc.2
      (fun z hz => hX z (List.mem_cons_of_mem _ hz))
    have := ih.head hc.1 (hX x (by simp))
    simpa using this

/-- Every reachable node is reachable within `n − 1` hops. -/
theorem reachesWithin_of_reaches [Fintype V] {X : Finset V} {a b : V} (h : Reaches G X a b) :
    ReachesWithin G X (Fintype.card V - 1) a b := by
  obtain ⟨p, ⟨⟨hh, hl, hc⟩, hn⟩, hX⟩ := h.exists_simplePath
  have := reachesWithin_of_chain p a b hh hl hc hX
  exact this.mono (by have := hn.length_le_card; omega)

/-! ## The fault-tolerant diameter -/

/-- `D` bounds the fault-tolerant diameter (equation (1)): for every `F` with `|F| ≤ f`, every
root `s` of `G_F` reaches every node of `G_F` by a path of length at most `D`
(i.e. `height(s, G_F) ≤ D`). -/
def FTDiamLE (G : Digraph V) (f D : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ f → ∀ s, IsRoot G F s → ∀ v, v ∉ F → ReachesWithin G F D s v

theorem FTDiamLE.mono {f D D' : ℕ} (h : FTDiamLE G f D) (hD : D ≤ D') : FTDiamLE G f D' :=
  fun F hF s hs v hv => (h F hF s hs v hv).mono hD

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
