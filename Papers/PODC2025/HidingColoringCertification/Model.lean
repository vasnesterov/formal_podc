import Mathlib

/-!
# Locally checkable proofs with one verification round

The model of Section 2 of [MMR25] (full version arXiv:2502.13854v1), specialised to one round
(`r = 1`), which is the only radius used by the results we formalize.

* `PortGraph`: a finite simple graph `G` with a port numbering (`port v w < deg v`, injective at
  every node), an injective identifier assignment `id : V → ℕ` with `id v < N`, and the value `N`
  given to every node (`N = poly(n)` in the paper; see `PortGraph.Admissible`).
* `View L`: the radius-1 view of a node in a labelled port graph: `N`, its own identifier, label
  and degree, and the multiset of the records of its neighbours (port at the centre, port at the
  neighbour, identifier, label and degree of the neighbour).  This is at least the information
  of the paper's view `(G¹ᵥ, prt|N(v), Id|N(v), I|N(v))` (we add the neighbours' degrees, which
  only makes the extracting algorithms stronger, hence the hiding results stronger).
* `AnonView L`: the same without identifiers (anonymous algorithms factor through `View.anon`).
* `LCP L`: a binary decoder `D : View L → Bool` with a set `sz n` of admissible certificates on
  `n`-node graphs ("certificates of size `f(n)`").

Properties (all relative to the global choice `bound : ℕ → ℕ`, `N = bound n`):
`Complete`, `Sound`, `StronglySound` (the paper's strong *promise* soundness),
`StronglySoundAll` (accepted nodes induce a bipartite graph in every instance), `Hiding`
(against every, possibly identifier-aware, extraction algorithm), `AnonHiding` (against
anonymous extraction algorithms) and `Anonymous`.
-/

-- CSLib candidate: one-round LCP model (port graphs with identifiers, views, LCP properties)

namespace Podc.HidingColoringCertification

open SimpleGraph Finset

/-- A class of graphs (the promise of a promise problem). -/
abbrev GraphClass := ∀ (V : Type), SimpleGraph V → Prop

/-- A finite simple graph with a port numbering, identifiers and the value `N` known to all
nodes. Ports are `0, …, deg v - 1` (the paper uses `1, …, deg v`). -/
structure PortGraph where
  /-- Nodes. -/
  V : Type
  [instFintype : Fintype V]
  [instDecEq : DecidableEq V]
  /-- The graph. -/
  G : SimpleGraph V
  [instDecRel : DecidableRel G.Adj]
  /-- `port v w` is the port of `v` leading to its neighbour `w`. -/
  port : V → V → ℕ
  port_lt : ∀ ⦃v w⦄, G.Adj v w → port v w < G.degree v
  port_inj : ∀ ⦃v w w'⦄, G.Adj v w → G.Adj v w' → port v w = port v w' → w = w'
  /-- Identifiers. -/
  id : V → ℕ
  id_inj : Function.Injective id
  /-- The common upper bound on the identifiers, known to every node. -/
  N : ℕ
  id_lt : ∀ v, id v < N

attribute [instance] PortGraph.instFintype PortGraph.instDecEq PortGraph.instDecRel

/-- What a node learns about one of its neighbours in one round. -/
structure NbrInfo (L : Type) where
  /-- Port at the centre. -/
  portHere : ℕ
  /-- Port at the neighbour. -/
  portThere : ℕ
  /-- Identifier of the neighbour. -/
  id : ℕ
  /-- Certificate of the neighbour. -/
  label : L
  /-- Degree of the neighbour. -/
  deg : ℕ
  deriving DecidableEq

/-- The radius-1 view of a node. -/
structure View (L : Type) where
  N : ℕ
  id : ℕ
  label : L
  deg : ℕ
  nbrs : Multiset (NbrInfo L)
  deriving DecidableEq

/-- Neighbour record without identifier. -/
structure AnonNbrInfo (L : Type) where
  portHere : ℕ
  portThere : ℕ
  label : L
  deg : ℕ
  deriving DecidableEq

/-- Radius-1 view without identifiers. -/
structure AnonView (L : Type) where
  N : ℕ
  label : L
  deg : ℕ
  nbrs : Multiset (AnonNbrInfo L)
  deriving DecidableEq

/-- Forget the identifier of a neighbour record. -/
def NbrInfo.anon {L : Type} (x : NbrInfo L) : AnonNbrInfo L :=
  ⟨x.portHere, x.portThere, x.label, x.deg⟩

/-- Forget all identifiers of a view. -/
def View.anon {L : Type} (μ : View L) : AnonView L :=
  ⟨μ.N, μ.label, μ.deg, μ.nbrs.map NbrInfo.anon⟩

namespace PortGraph

variable {L : Type} (P : PortGraph)

/-- The record of neighbour `w` as seen from `v`. -/
def nbrInfo (ℓ : P.V → L) (v w : P.V) : NbrInfo L :=
  ⟨P.port v w, P.port w v, P.id w, ℓ w, P.G.degree w⟩

/-- The radius-1 view of `v` under the labelling `ℓ`. -/
def view (ℓ : P.V → L) (v : P.V) : View L :=
  ⟨P.N, P.id v, ℓ v, P.G.degree v, (P.G.neighborFinset v).val.map (P.nbrInfo ℓ v)⟩

lemma mem_view_nbrs {ℓ : P.V → L} {v : P.V} {x : NbrInfo L} :
    x ∈ (P.view ℓ v).nbrs ↔ ∃ w, P.G.Adj v w ∧ P.nbrInfo ℓ v w = x := by
  simp [view, Multiset.mem_map]

lemma nbrInfo_mem_view {ℓ : P.V → L} {v w : P.V} (h : P.G.Adj v w) :
    P.nbrInfo ℓ v w ∈ (P.view ℓ v).nbrs :=
  P.mem_view_nbrs.2 ⟨w, h, rfl⟩

lemma view_eq_mk {ℓ : P.V → L} {v : P.V} (s : Finset P.V) (hs : ∀ w, P.G.Adj v w ↔ w ∈ s) :
    P.view ℓ v = ⟨P.N, P.id v, ℓ v, s.card, s.val.map (P.nbrInfo ℓ v)⟩ := by
  have : P.G.neighborFinset v = s := by ext w; simp [hs]
  simp only [view, ← this, card_neighborFinset_eq_degree]

/-- `n ≤ N`: identifiers are injective into `[0, N)`. -/
lemma card_le_N : Fintype.card P.V ≤ P.N := by
  have := Fintype.card_le_of_injective (fun v => (⟨P.id v, P.id_lt v⟩ : Fin P.N))
    (fun a b h => P.id_inj (by simpa using h))
  simpa using this

/-- Standard port numbering of a graph on `Fin n`: neighbours in increasing order. -/
def stdPort {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n) : ℕ :=
  ((G.neighborFinset v).filter (· < w)).card

/-- A graph on `Fin n` with the standard port numbering, identifiers `i ↦ i`, and `N ≥ n`. -/
abbrev ofFin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (N : ℕ) (hN : n ≤ N) :
    PortGraph where
  V := Fin n
  G := G
  port := stdPort G
  port_lt := fun {v w} h => by
    rw [← card_neighborFinset_eq_degree]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun hs => ?_⟩
    have := hs ((mem_neighborFinset _ _ _).2 h)
    simp at this
  port_inj := fun {v w w'} h h' e => by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : ((G.neighborFinset v).filter (· < w)).card <
          ((G.neighborFinset v).filter (· < w')).card := by
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun hs => ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
        · have := hs (Finset.mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 h, hlt⟩); simp at this
      simp only [stdPort] at e; omega
    · have : ((G.neighborFinset v).filter (· < w')).card <
          ((G.neighborFinset v).filter (· < w)).card := by
        apply Finset.card_lt_card
        refine ⟨fun x hx => ?_, fun hs => ?_⟩
        · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
        · have := hs (Finset.mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 h', hlt⟩); simp at this
      simp only [stdPort] at e; omega
  id := fun v => v.val
  id_inj := fun a b h => Fin.ext h
  N := N
  id_lt v := lt_of_lt_of_le v.isLt hN

/-- The instance uses the prescribed value `N = bound n`. -/
def Admissible (bound : ℕ → ℕ) : Prop := P.N = bound (Fintype.card P.V)

end PortGraph

/-- A one-round locally checkable proof: a binary decoder and the admissible certificates on
`n`-node graphs. -/
structure LCP (L : Type) where
  /-- The verifier. -/
  D : View L → Bool
  /-- Admissible certificates on `n`-node instances. -/
  sz : ℕ → Set L

namespace LCP

variable {L : Type} (S : LCP L) (bound : ℕ → ℕ)

/-- `v` accepts. -/
def Acc (P : PortGraph) (ℓ : P.V → L) (v : P.V) : Prop := S.D (P.view ℓ v) = true

instance (P : PortGraph) (ℓ : P.V → L) : DecidablePred (S.Acc P ℓ) :=
  fun v => inferInstanceAs (Decidable (S.D (P.view ℓ v) = true))

/-- `ℓ` is a labelling of admissible size. -/
def SizeOK (P : PortGraph) (ℓ : P.V → L) : Prop := ∀ v, ℓ v ∈ S.sz (Fintype.card P.V)

/-- Completeness for the promise problem `2-col_H` (more generally `k-col_H`): on every graph of
`H`, for every port and identifier assignment, some admissible labelling is accepted
everywhere. -/
def Complete (H : GraphClass) : Prop :=
  ∀ P : PortGraph, P.Admissible bound → H P.V P.G →
    ∃ ℓ : P.V → L, S.SizeOK P ℓ ∧ ∀ v, S.Acc P ℓ v

/-- Soundness for `k-col`: on a graph that is not `k`-colourable some node rejects. -/
def Sound (k : ℕ) : Prop :=
  ∀ P : PortGraph, P.Admissible bound → ¬ P.G.Colorable k →
    ∀ ℓ : P.V → L, S.SizeOK P ℓ → ∃ v, ¬ S.Acc P ℓ v

/-- The subgraph induced by the accepting nodes. -/
def accGraph (P : PortGraph) (ℓ : P.V → L) : SimpleGraph {v // S.Acc P ℓ v} :=
  P.G.induce {v | S.Acc P ℓ v}

/-- Strong (promise) soundness (Section 2.5 of [MMR25]): on every graph that is not
`k`-colourable, the accepting nodes induce a `k`-colourable graph. -/
def StronglySound (k : ℕ) : Prop :=
  ∀ P : PortGraph, P.Admissible bound → ¬ P.G.Colorable k →
    ∀ ℓ : P.V → L, S.SizeOK P ℓ → (S.accGraph P ℓ).Colorable k

/-- Strong soundness on *all* graphs (Section 2.3 of [MMR25]), for arbitrary labellings. -/
def StronglySoundAll (k : ℕ) : Prop :=
  ∀ P : PortGraph, ∀ ℓ : P.V → L, (S.accGraph P ℓ).Colorable k

variable {S bound} in
lemma StronglySoundAll.stronglySound {k : ℕ} (h : S.StronglySoundAll k) :
    S.StronglySound bound k :=
  fun P _ _ ℓ _ => h P ℓ

variable {S bound} in
/-- Strong soundness implies soundness. -/
lemma StronglySound.sound {k : ℕ} (h : S.StronglySound bound k) : S.Sound bound k := by
  intro P hP hc ℓ hℓ
  by_contra hall
  push Not at hall
  apply hc
  obtain ⟨c⟩ := h P hP hc ℓ hℓ
  exact ⟨Coloring.mk (fun v => c ⟨v, hall v⟩) (fun {a b} hab => c.valid (by simpa [accGraph]))⟩

/-- An extraction algorithm `A` fails on the labelled instance if it does not output a proper
`k`-colouring, i.e. two neighbours get the same output. -/
def Fails {k : ℕ} (A : View L → Fin k) (P : PortGraph) (ℓ : P.V → L) : Prop :=
  ∃ u v, P.G.Adj u v ∧ A (P.view ℓ u) = A (P.view ℓ v)

/-- Hiding (Section 2.4 of [MMR25]): every extraction algorithm fails on some admissible,
everywhere-accepted, admissibly labelled instance whose graph is in `H`. -/
def Hiding (H : GraphClass) (k : ℕ) : Prop :=
  ∀ A : View L → Fin k, ∃ P : PortGraph, P.Admissible bound ∧ H P.V P.G ∧
    ∃ ℓ : P.V → L, S.SizeOK P ℓ ∧ (∀ v, S.Acc P ℓ v) ∧ Fails A P ℓ

/-- Hiding against anonymous extraction algorithms (used for anonymous LCPs). -/
def AnonHiding (H : GraphClass) (k : ℕ) : Prop :=
  ∀ A : AnonView L → Fin k, ∃ P : PortGraph, P.Admissible bound ∧ H P.V P.G ∧
    ∃ ℓ : P.V → L, S.SizeOK P ℓ ∧ (∀ v, S.Acc P ℓ v) ∧ Fails (A ∘ View.anon) P ℓ

variable {S bound} in
lemma Hiding.anonHiding {H : GraphClass} {k : ℕ} (h : S.Hiding bound H k) :
    S.AnonHiding bound H k :=
  fun A => h (A ∘ View.anon)

/-- The decoder does not look at identifiers. -/
def Anonymous : Prop := ∀ μ μ' : View L, μ.anon = μ'.anon → S.D μ = S.D μ'

end LCP

/-- Bipartite graphs, i.e. `G(2-col)`. -/
def Bipartite : GraphClass := fun _ G => G.Colorable 2

end Podc.HidingColoringCertification
