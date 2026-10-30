import Cslib.Foundations.Relation.RelatesInSteps
import Cslib.Computability.Distributed.Congest.LowerBound
import Mathlib

/-!
# Directed spanners and the distributed directed `k`-spanner problem

Definitions from §1.5 of Censor-Hillel–Dory, *Distributed Spanner Approximation* (PODC 2018).

* A digraph on `V` is a finset of arcs `E : Finset (V × V)`.
* `IsDiSpanner E H k`: `H ⊆ E` and every arc `(u, v) ∈ E` is joined in `H` by a directed walk of
  length `≤ k` (a walk can be shortened to a path, so this is the paper's notion).
* `IsApproxDiSpanner α E H k`: `H` is a `k`-spanner with `|H| ≤ α · |H'|` for every `k`-spanner `H'`.
* Distributed setting: the communication network is the underlying undirected graph `net E`
  (communication is bidirectional), node `v` initially knows the IDs of its neighbours and the
  directions of its incident arcs (`view E v`), and every node outputs a set of incident arcs; the
  output spanner is the union (`outArcs`). Selectors `pick v s u w` are only queried for
  `v ∈ {u, w}`.
-/

namespace Podc.SpannerApproximation

open Finset Relation Cslib.Congest

variable {V : Type*}

/-- The arc relation of a finite digraph. -/
def arcRel (E : Finset (V × V)) (u v : V) : Prop := (u, v) ∈ E

/-- `H` is a directed `k`-spanner of the digraph `E`. -/
def IsDiSpanner (E H : Finset (V × V)) (k : ℕ) : Prop :=
  H ⊆ E ∧ ∀ e ∈ E, RelatesWithinSteps (arcRel H) e.1 e.2 k

/-- `H` is an `α`-approximate minimum directed `k`-spanner of `E`. -/
def IsApproxDiSpanner (α : ℝ) (E H : Finset (V × V)) (k : ℕ) : Prop :=
  IsDiSpanner E H k ∧ ∀ H', IsDiSpanner E H' k → (H.card : ℝ) ≤ α * H'.card

/-- A spanner of a smaller stretch is a spanner of a larger stretch. -/
lemma IsDiSpanner.mono {E H : Finset (V × V)} {k k' : ℕ} (h : IsDiSpanner E H k) (hk : k ≤ k') :
    IsDiSpanner E H k' :=
  ⟨h.1, fun e he => RelatesWithinSteps.mono hk (h.2 e he)⟩

/-- The communication network of a digraph: its underlying undirected graph. -/
def net (E : Finset (V × V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u, v) ∈ E ∨ (v, u) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance [DecidableEq V] (E : Finset (V × V)) : DecidableRel (net E).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ E ∨ (v, u) ∈ E)))

/-- The input of node `v`: for every `w`, whether `(v, w)` and `(w, v)` are arcs. -/
def view [DecidableEq V] (E : Finset (V × V)) (v : V) : V → Bool × Bool :=
  fun w => (decide ((v, w) ∈ E), decide ((w, v) ∈ E))

/-- The node input type of a directed network. -/
abbrev DInput (V : Type*) := V → Bool × Bool

/-- The arcs output by the nodes in states `st`: `(u, w)` is taken iff one of its endpoints
selects it. -/
def selected [Fintype V] {σ : Type*} (pick : V → σ → V → V → Bool) (st : V → σ) :
    Finset (V × V) :=
  univ.filter fun e => (pick e.1 (st e.1) e.1 e.2 || pick e.2 (st e.2) e.1 e.2) = true

/-- The spanner output by a deterministic CONGEST algorithm after `T` rounds on the digraph `E`. -/
def outArcs [Fintype V] [DecidableEq V] {σ : Type*} {B : ℕ} (A : Algorithm V (DInput V) σ B)
    (pick : V → σ → V → V → Bool) (E : Finset (V × V)) (T : ℕ) : Finset (V × V) :=
  selected pick (A.run (net E) (view E) T)

/-- The spanner output by a randomized CONGEST algorithm (random strings `r`) after `T` rounds. -/
def outArcsR [Fintype V] [DecidableEq V] {σ ρ : Type*} {B : ℕ}
    (A : Algorithm V (DInput V × ρ) σ B) (pick : V → σ → V → V → Bool) (E : Finset (V × V))
    (T : ℕ) (r : V → ρ) : Finset (V × V) :=
  selected pick (A.run (net E) (fun v => (view E v, r v)) T)

/-- Number of random strings on which a randomized algorithm does not output an `α`-approximate
minimum `k`-spanner of `E`. -/
noncomputable def failCount [Fintype V] [DecidableEq V] {σ ρ : Type*} [Fintype ρ] {B : ℕ}
    (A : Algorithm V (DInput V × ρ) σ B) (pick : V → σ → V → V → Bool) (E : Finset (V × V))
    (T : ℕ) (α : ℝ) (k : ℕ) : ℕ := by
  classical
  exact (univ.filter fun r : V → ρ => ¬ IsApproxDiSpanner α E (outArcsR A pick E T r) k).card

/-- Arcs inside a set `S` selected in states `st` only depend on the states of nodes of `S`. -/
lemma selected_inter_eq [Fintype V] [DecidableEq V] {σ : Type*} (pick : V → σ → V → V → Bool) {st st' : V → σ}
    (S : V → Prop) (D : Finset (V × V)) (hD : ∀ e ∈ D, S e.1 ∧ S e.2)
    (h : ∀ v, S v → st v = st' v) : selected pick st ∩ D = selected pick st' ∩ D := by
  ext e
  simp only [selected, mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h _ (hD e h2).1, ← h _ (hD e h2).2]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h _ (hD e h2).1, h _ (hD e h2).2]
    exact ⟨h1, h2⟩

/-! ### Transport along a bijection of vertex sets -/

/-- Image of a digraph under a bijection of vertex sets. -/
def mapArcs {W : Type*} (e : V ≃ W) (E : Finset (V × V)) : Finset (W × W) :=
  E.map (e.prodCongr e).toEmbedding

@[simp] lemma mem_mapArcs {W : Type*} (e : V ≃ W) (E : Finset (V × V)) (p : W × W) :
    p ∈ mapArcs e E ↔ (e.symm p.1, e.symm p.2) ∈ E := by
  simp only [mapArcs, mem_map_equiv]
  rfl

lemma card_mapArcs {W : Type*} (e : V ≃ W) (E : Finset (V × V)) :
    (mapArcs e E).card = E.card := card_map _

lemma relatesWithinSteps_mapArcs {W : Type*} (e : V ≃ W) (H : Finset (V × V)) {u v : V} {k : ℕ} :
    RelatesWithinSteps (arcRel (mapArcs e H)) (e u) (e v) k ↔
      RelatesWithinSteps (arcRel H) u v k := by
  constructor
  · intro h
    have := RelatesWithinSteps.map (r := arcRel (mapArcs e H)) (r' := arcRel H) e.symm
      (fun a b hab => by simpa [arcRel] using hab) h
    simpa using this
  · intro h
    exact RelatesWithinSteps.map (r := arcRel H) (r' := arcRel (mapArcs e H)) e
      (fun a b hab => by simpa [arcRel] using hab) h

/-- Spanners are preserved by relabelling. -/
lemma isDiSpanner_mapArcs {W : Type*} (e : V ≃ W) {E H : Finset (V × V)} {k : ℕ} :
    IsDiSpanner (mapArcs e E) (mapArcs e H) k ↔ IsDiSpanner E H k := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · have := h1 ((mem_mapArcs e H (e p.1, e p.2)).2 (by simpa using hp))
      simpa using this
    · have := h2 (e p.1, e p.2) (by simpa using hp)
      exact (relatesWithinSteps_mapArcs e H).1 this
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [mem_mapArcs] at hp ⊢; exact h1 hp
    · rw [mem_mapArcs] at hp
      have := (relatesWithinSteps_mapArcs e H (u := e.symm p.1) (v := e.symm p.2)).2 (h2 _ hp)
      simpa using this

lemma mapArcs_symm_mapArcs {W : Type*} (e : V ≃ W) (H : Finset (W × W)) :
    mapArcs e (mapArcs e.symm H) = H := by
  ext p; simp

end Podc.SpannerApproximation
