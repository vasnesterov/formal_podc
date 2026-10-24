import Papers.PODC2010.ArbdefectiveColoring.Basic

/-!
# Locality tools: running an algorithm on all colour classes in parallel

Round complexity is expressed with CSLib's extensional locality `Cslib.Local.IsLocal R f`
("`f G x v` only depends on the radius-`R` view of `v`", i.e. `f` is computed by an `R`-round
LOCAL algorithm). This file adds:

* `IsLocalG R f`: locality of an algorithm `f : SimpleGraph V → V → β` without inputs (the vertices
  are their own identifiers).
* `isLocal_classGraph` (CSLib candidate): running an `σ`-round algorithm in parallel on all the
  subgraphs induced by the classes of a labelling (i.e. on `classGraph G (κ ∘ x)`) is again an
  `σ`-round algorithm. This is how the recursive procedures of the paper ("for each `Gᵢ` in
  parallel do") are composed.
* `isLocal_one_nbr` (CSLib candidate): a function of a vertex's own label and its neighbours'
  labels is `1`-local.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- A graph algorithm without inputs runs in `R` rounds of the LOCAL model. -/
def IsLocalG {β : Type*} (R : ℕ) (f : SimpleGraph V → V → β) : Prop :=
  IsLocal R (fun G (_ : V → Unit) v => f G v)

lemma IsLocalG.mono {β : Type*} {R R' : ℕ} {f : SimpleGraph V → V → β} (h : IsLocalG R f)
    (hR : R ≤ R') : IsLocalG R' f := IsLocal.mono h hR

/-- An algorithm without inputs, viewed as an algorithm with (ignored) inputs. -/
lemma IsLocalG.isLocal {α β : Type*} {R : ℕ} {f : SimpleGraph V → V → β} (h : IsLocalG R f) :
    IsLocal R (fun G (_ : V → α) v => f G v) :=
  fun G _ G' _ v hv => h G (fun _ => ()) G' (fun _ => ()) v ⟨hv.1, fun _ _ => rfl⟩

-- CSLib candidate: `Cslib/Computability/Distributed/Local/Locality.lean` (`IsLocal.map`, `IsLocal.prod`,
-- `isLocal_self`, `isLocal_classGraph`, `isLocal_one_nbr`)
/-- Post-processing the output of a local algorithm does not cost rounds. -/
lemma IsLocal.map {α β γ : Type*} {R : ℕ} {f : SimpleGraph V → (V → α) → V → β}
    (hf : IsLocal R f) (φ : β → γ) : IsLocal R (fun G x v => φ (f G x v)) :=
  fun G x G' x' v hv => by beta_reduce; rw [hf G x G' x' v hv]

/-- Two local algorithms can be run in parallel. -/
lemma IsLocal.prod {α β γ : Type*} {R : ℕ} {f : SimpleGraph V → (V → α) → V → β}
    {g : SimpleGraph V → (V → α) → V → γ} (hf : IsLocal R f) (hg : IsLocal R g) :
    IsLocal R (fun G x v => (f G x v, g G x v)) :=
  fun G x G' x' v hv => by beta_reduce; rw [hf G x G' x' v hv, hg G x G' x' v hv]

/-- A vertex knows its own input. -/
lemma isLocal_self {α β : Type*} (φ : V → α → β) : IsLocal (V := V) 0 (fun _ x v => φ v (x v)) :=
  fun _ _ _ _ v hv => by beta_reduce; rw [hv.2 v (by simp)]

/-- Distances in a subgraph are at least the distances in the graph. -/
lemma edist_le_of_le {G H : SimpleGraph V} (hHG : H ≤ G) (u v : V) : G.edist u v ≤ H.edist u v :=
  SimpleGraph.edist_anti hHG

/-- **Parallel runs on colour classes.** If `g` is an `σ`-round algorithm, then running `g` on the
subgraph `classGraph G (κ ∘ x)` (all classes of the labelling `κ ∘ x` in parallel; a vertex only
communicates with neighbours in its own class) is an `σ`-round algorithm on `(G, x)`. -/
lemma isLocal_classGraph {α β γ : Type*} {σ : ℕ} {g : SimpleGraph V → (V → α) → V → γ}
    (hg : IsLocal σ g) (κ : α → β) :
    IsLocal σ (fun G x => g (classGraph G (κ ∘ x)) x) := by
  intro G x G' x' v hv
  refine hg _ _ _ _ _ ⟨fun y hy z => ?_, fun u hu => hv.2 u
    ((edist_le_of_le (classGraph_le G _) v u).trans hu)⟩
  have hy' : G.edist v y < σ := (edist_le_of_le (classGraph_le G _) v y).trans_lt hy
  have hyx : x y = x' y := hv.2 y hy'.le
  have hGG := hv.1 hy' z
  simp only [classGraph_adj, Function.comp_apply]
  by_cases hyz : G.Adj y z
  · have hz : G.edist v z ≤ σ := by
      calc G.edist v z ≤ G.edist v y + G.edist y z := SimpleGraph.edist_triangle
        _ = G.edist v y + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.2 hyz]
        _ ≤ σ := Order.add_one_le_of_lt hy'
    rw [hyx, hv.2 z hz]
    exact and_congr_left' hGG
  · simp only [hyz, false_and, false_iff, not_and]
    exact fun h => absurd (hGG.2 h) hyz

/-- `isLocal_classGraph` for algorithms without inputs. -/
lemma IsLocalG.classGraph {α β γ : Type*} {σ : ℕ} {f : SimpleGraph V → V → γ}
    (hf : IsLocalG σ f) (κ : α → β) :
    IsLocal σ (fun G (x : V → α) v => f (classGraph G (κ ∘ x)) v) :=
  isLocal_classGraph (g := fun G (_ : V → α) v => f G v) hf.isLocal κ

/-- The neighbourhood view of `v`: the labels of its neighbours (`none` for non-neighbours). -/
noncomputable def nbrView {α : Type*} (G : SimpleGraph V) (x : V → α) (v : V) : V → Option α :=
  fun u => if G.Adj v u then some (x u) else none

/-- A function of the own label and the neighbours' labels is computed in one round. -/
lemma isLocal_one_nbr {α β : Type*} (Φ : V → α → (V → Option α) → β) :
    IsLocal (V := V) 1 (fun G x v => Φ v (x v) (nbrView G x v)) := by
  intro G x G' x' v hv
  have hself := hv.2 v (by simp)
  have hnb : nbrView G x v = nbrView G' x' v := by
    funext u
    simp only [nbrView]
    have hadj := hv.1.adj_iff one_pos u
    by_cases h : G.Adj v u
    · rw [ite_eq_left h, ite_eq_left (hadj.1 h),
        hv.2 u (by rw [SimpleGraph.edist_eq_one_iff_adj.2 h]; simp)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hadj.2 h'))]
  simp only [hself, hnb]

end Podc.ArbdefectiveColoring
