import Mathlib.Combinatorics.SimpleGraph.Diam
import Cslib.Computability.Distributed.Congest.LowerBound
import Mathlib.Tactic.Linarith
import Podc.Computability.Distributed.Congest.GatherInputs
import Cslib.Computability.Distributed.Congest.Gather
import Cslib.Computability.Distributed.Congest.Randomized
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The `(+,1)`-approximation lower bound for the diameter (Theorem 4 of [HW12])

Holzer–Wattenhofer, *Optimal Distributed All Pairs Shortest Paths and Applications*, PODC 2012,
Section 5.2 (Theorem 4, Lemmas 8, 9, Claim 2) and the `(+,1)` part of Lemma 10.

Model: deterministic (resp. private-coin randomized) synchronous CONGEST with `B`-bit messages,
node IDs = the vertex type `V` with `|V| = n`, node input = adjacency row (CSLib
`Cslib.Congest.Algorithm`, `LBFamily.ofAdj`).

## The graphs `G_{a,b}` (`gr a b` on `DV k p fa fb`, `d = 2p + 2`)

Alice: `l_ν` (`lu ν`, upper, `ν < k`), `l_μ` (`ll μ`, lower), paths `T^a_ν = l_ν – ta ν 0 – … –
ta ν (p-1)` of length `p` (`l'_ν = ta ν (p-1)`), `c₀, c₁`, fill-up nodes `wa j`. Bob symmetric
(`ru, rl, tb, c₂, c₃, wb`), with the paths at the *lower* nodes `r_μ`. Edges: `l_ν l_μ` iff
`a (ν, μ) = 0`, `r_ν r_μ` iff `b (ν, μ) = 0`, `c₀ – l_upper`, `c₁ – l_lower`, `c₀ c₁`,
`w^a – {l_upper, c₀, c₁}`, and symmetrically for Bob; cut: `l_i r_i` (`i < 2k`) and `c₀ c₂`.
The bits are indexed by `(ν, μ) ∈ Fin k × Fin k` (the paper's index `k(μ - k + 1) + ν` is out of
range; Figure 1 uses `kν + (μ - k)`).

## Main results

* `lemma8`: not disjoint ⇒ `diam G_{a,b} = d + 2` (witness `le_edist_last_of_inter`:
  `d(l'_ν, r'_μ) ≥ d + 2`, via a Lipschitz potential; upper bound `edist_le_two_mul_add_four`).
* `lemma9`: disjoint ⇔ `diam G_{a,b} = d` (for `k ≥ 1`); `claim2`; `diam_mem`, `gr_connected`.
* `theorem4`: deterministic Theorem 4: `k² ≤ T · 2 (2k + 1) B + 2` with `k = ⌊(n-4)/(d+2)⌋`;
  `theorem4_bound`: `k ≤ 4 T B + 2`, i.e. `T = Ω(n / (D B))`.
* `theorem4_randomized`: the same with `κ k²` on the left, conditional on the randomized
  communication lower bound for DISJ (`RandDisjLB`, Theorem 2 of the paper, not proved).
* `lemma10_eccent_plusOne`, `lemma10_apsp_plusOne`: the `(+,1)` parts of Lemma 10 (eccentricities, APSP) on the
  same family (all-nodes-accept convention: no max-aggregation needed).
* `theorem4_hyp_satisfiable`, `lemma10_apsp_plusOne_hyp_satisfiable`: non-vacuity (flooding).

Upper bounds on distances use descent certificates to four hubs `c₀ … c₃` (`edist_le_of_descent`,
`h0 … h3`), lower bounds 1-Lipschitz potentials (`le_edist_of_lipschitz`, `pot1`, `pot2`).
-/

namespace Podc.OptimalAPSP

open SimpleGraph Cslib.Congest Cslib.CommunicationComplexity Cslib.CommunicationComplexity.Protocol

/-- The vertices of the lower-bound graph `G_{a,b}`. -/
inductive DV (k p fa fb : ℕ) where
  | lu (ν : Fin k)
  | ll (μ : Fin k)
  | ta (ν : Fin k) (j : Fin p)
  | c0
  | c1
  | wa (j : Fin fa)
  | ru (ν : Fin k)
  | rl (μ : Fin k)
  | tb (μ : Fin k) (j : Fin p)
  | c2
  | c3
  | wb (j : Fin fb)
  deriving DecidableEq

variable {k p fa fb : ℕ}

namespace DV

/-- Edges (one direction). -/
def eb (a b : Fin k × Fin k → Bool) : DV k p fa fb → DV k p fa fb → Bool
  | lu ν, ll μ => !a (ν, μ)
  | lu ν, ta ν' j => decide (ν = ν' ∧ j.val = 0)
  | ta ν j, ta ν' j' => decide (ν = ν' ∧ j'.val = j.val + 1)
  | c0, lu _ => true
  | c1, ll _ => true
  | c0, c1 => true
  | wa _, lu _ => true
  | wa _, c0 => true
  | wa _, c1 => true
  | ru ν, rl μ => !b (ν, μ)
  | rl μ, tb μ' j => decide (μ = μ' ∧ j.val = 0)
  | tb μ j, tb μ' j' => decide (μ = μ' ∧ j'.val = j.val + 1)
  | c2, ru _ => true
  | c3, rl _ => true
  | c2, c3 => true
  | wb _, ru _ => true
  | wb _, c2 => true
  | wb _, c3 => true
  | lu ν, ru ν' => decide (ν = ν')
  | ll μ, rl μ' => decide (μ = μ')
  | c0, c2 => true
  | _, _ => false

lemma eb_irrefl (a b : Fin k × Fin k → Bool) (x : DV k p fa fb) : eb a b x x = false := by
  cases x <;> simp [eb]

end DV

open DV

/-- The lower-bound graph `G_{a,b}` of Theorem 4 on its own vertex type. -/
def gr (a b : Fin k × Fin k → Bool) : SimpleGraph (DV k p fa fb) where
  Adj x y := eb a b x y = true ∨ eb a b y x = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by simp [eb_irrefl] at h⟩

instance (a b : Fin k × Fin k → Bool) : DecidableRel (gr (p := p) (fa := fa) (fb := fb) a b).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma gr_adj {a b : Fin k × Fin k → Bool} {x y : DV k p fa fb} :
    (gr a b).Adj x y ↔ eb a b x y = true ∨ eb a b y x = true := Iff.rfl

/-! ### Distance tools -/

-- CSLib candidate: `le_edist_of_lipschitz`, `edist_le_of_descent`, `hom_edist_le`,
-- `edist_comap_equiv`, `ediam_comap_equiv`, `eccent_comap_equiv` (general graph metric facts).

section Tools

variable {V W : Type*}

/-- A Lipschitz potential bounds distances from below. -/
lemma le_edist_of_lipschitz {G : SimpleGraph V} (f : V → ℕ)
    (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) (u v : V) : ((f v - f u : ℕ) : ℕ∞) ≤ G.edist u v := by
  have key : ∀ {x y : V} (w : G.Walk x y), f y ≤ f x + w.length := by
    intro x y w
    induction w with
    | nil => simp
    | cons h w ih => have := hf _ _ h; simp only [Walk.length_cons]; omega
  rw [SimpleGraph.edist]
  refine le_iInf fun w => ?_
  have := key w
  exact_mod_cast (by omega : f v - f u ≤ w.length)

/-- A descent certificate bounds distances to a target from above. -/
lemma edist_le_of_descent {G : SimpleGraph V} (f : V → ℕ) (t : V)
    (hf : ∀ x, x ≠ t → ∃ y, G.Adj x y ∧ f y < f x) (x : V) : G.edist x t ≤ f x := by
  induction h : f x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases hx : x = t
    · subst hx; simp
    obtain ⟨y, hxy, hy⟩ := hf x hx
    calc G.edist x t ≤ G.edist x y + G.edist y t := G.edist_triangle
      _ ≤ 1 + (f y : ℕ∞) := add_le_add (edist_eq_one_iff_adj.2 hxy).le (ih _ (h ▸ hy) y rfl)
      _ ≤ m := by rw [← h]; exact_mod_cast (by omega : 1 + f y ≤ f x)

/-- Graph homomorphisms do not increase distances. -/
lemma hom_edist_le {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G →g G') (a b : V) :
    G'.edist (φ a) (φ b) ≤ G.edist a b := by
  by_cases h : G.Reachable a b
  · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_edist
    rw [← hw]
    simpa using SimpleGraph.edist_le (w.map φ)
  · simp [edist_eq_top_of_not_reachable h]

/-- Relabelling along an equivalence preserves distances. -/
lemma edist_comap_equiv (G : SimpleGraph W) (e : V ≃ W) (u v : V) :
    (G.comap e).edist u v = G.edist (e u) (e v) := by
  apply le_antisymm
  · have := hom_edist_le (Iso.comap e G).symm.toHom (e u) (e v)
    simpa using this
  · exact hom_edist_le (Iso.comap e G).toHom u v

lemma ediam_comap_equiv (G : SimpleGraph W) (e : V ≃ W) : (G.comap e).ediam = G.ediam := by
  apply le_antisymm
  · exact ediam_le_iff.2 fun u v => by rw [edist_comap_equiv]; exact edist_le_ediam
  · refine ediam_le_iff.2 fun u v => ?_
    have := edist_le_ediam (G := G.comap e) (u := e.symm u) (v := e.symm v)
    rwa [edist_comap_equiv, e.apply_symm_apply, e.apply_symm_apply] at this

lemma eccent_comap_equiv (G : SimpleGraph W) (e : V ≃ W) (v : V) :
    (G.comap e).eccent v = G.eccent (e v) := by
  apply le_antisymm
  · exact (eccent_le_iff _ _).2 fun u => by rw [edist_comap_equiv]; exact edist_le_eccent
  · refine (eccent_le_iff _ _).2 fun u => ?_
    have := edist_le_eccent (G := G.comap e) (u := v) (v := e.symm u)
    rwa [edist_comap_equiv, e.apply_symm_apply] at this

end Tools

/-! ### Upper bounds on distances: four hubs -/

section Upper

variable (a b : Fin k × Fin k → Bool)

lemma ta_step (ν : Fin k) (j : Fin p) :
    ∃ y, (gr (p := p) (fa := fa) (fb := fb) a b).Adj (ta ν j) y ∧
    ((j.val = 0 ∧ y = lu ν) ∨ ∃ j' : Fin p, j'.val + 1 = j.val ∧ y = ta ν j') := by
  by_cases hj : j.val = 0
  · exact ⟨lu ν, by simp [gr_adj, eb, hj], Or.inl ⟨hj, rfl⟩⟩
  · refine ⟨ta ν ⟨j.val - 1, by omega⟩, by simp [gr_adj, eb]; omega, Or.inr ⟨_, ?_, rfl⟩⟩
    simp; omega

lemma tb_step (μ : Fin k) (j : Fin p) :
    ∃ y, (gr (p := p) (fa := fa) (fb := fb) a b).Adj (tb μ j) y ∧
    ((j.val = 0 ∧ y = rl μ) ∨ ∃ j' : Fin p, j'.val + 1 = j.val ∧ y = tb μ j') := by
  by_cases hj : j.val = 0
  · exact ⟨rl μ, by simp [gr_adj, eb, hj], Or.inl ⟨hj, rfl⟩⟩
  · refine ⟨tb μ ⟨j.val - 1, by omega⟩, by simp [gr_adj, eb]; omega, Or.inr ⟨_, ?_, rfl⟩⟩
    simp; omega

/-- Distance bound to the hub `c0`. -/
def h0 : DV k p fa fb → ℕ
  | lu _ => 1 | ll _ => 2 | ta _ j => j.val + 2 | c0 => 0 | c1 => 1 | wa _ => 1
  | ru _ => 2 | rl _ => 3 | tb _ j => j.val + 4 | c2 => 1 | c3 => 2 | wb _ => 2

/-- Distance bound to the hub `c1`. -/
def h1 : DV k p fa fb → ℕ
  | lu _ => 2 | ll _ => 1 | ta _ j => j.val + 3 | c0 => 1 | c1 => 0 | wa _ => 1
  | ru _ => 3 | rl _ => 2 | tb _ j => j.val + 3 | c2 => 2 | c3 => 3 | wb _ => 3

/-- Distance bound to the hub `c2`. -/
def h2 : DV k p fa fb → ℕ
  | lu _ => 2 | ll _ => 3 | ta _ j => j.val + 3 | c0 => 1 | c1 => 2 | wa _ => 2
  | ru _ => 1 | rl _ => 2 | tb _ j => j.val + 3 | c2 => 0 | c3 => 1 | wb _ => 1

/-- Distance bound to the hub `c3`. -/
def h3 : DV k p fa fb → ℕ
  | lu _ => 3 | ll _ => 2 | ta _ j => j.val + 4 | c0 => 2 | c1 => 3 | wa _ => 3
  | ru _ => 2 | rl _ => 1 | tb _ j => j.val + 2 | c2 => 1 | c3 => 0 | wb _ => 1

lemma edist_c0 (x : DV k p fa fb) : (gr a b).edist x c0 ≤ h0 x := by
  refine edist_le_of_descent _ _ (fun x hx => ?_) x
  cases x with
  | lu ν => exact ⟨c0, by simp [gr_adj, eb], by simp [h0]⟩
  | ll μ => exact ⟨c1, by simp [gr_adj, eb], by simp [h0]⟩
  | ta ν j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := ta_step a b ν j <;>
      exact ⟨_, hy, by simp [h0] <;> omega⟩
  | c0 => exact absurd rfl hx
  | c1 => exact ⟨c0, by simp [gr_adj, eb], by simp [h0]⟩
  | wa _ => exact ⟨c0, by simp [gr_adj, eb], by simp [h0]⟩
  | ru ν => exact ⟨c2, by simp [gr_adj, eb], by simp [h0]⟩
  | rl μ => exact ⟨c3, by simp [gr_adj, eb], by simp [h0]⟩
  | tb μ j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := tb_step a b μ j <;>
      exact ⟨_, hy, by simp [h0] <;> omega⟩
  | c2 => exact ⟨c0, by simp [gr_adj, eb], by simp [h0]⟩
  | c3 => exact ⟨c2, by simp [gr_adj, eb], by simp [h0]⟩
  | wb _ => exact ⟨c2, by simp [gr_adj, eb], by simp [h0]⟩

lemma edist_c1 (x : DV k p fa fb) : (gr a b).edist x c1 ≤ h1 x := by
  refine edist_le_of_descent _ _ (fun x hx => ?_) x
  cases x with
  | lu ν => exact ⟨c0, by simp [gr_adj, eb], by simp [h1]⟩
  | ll μ => exact ⟨c1, by simp [gr_adj, eb], by simp [h1]⟩
  | ta ν j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := ta_step a b ν j <;>
      exact ⟨_, hy, by simp [h1] <;> omega⟩
  | c0 => exact ⟨c1, by simp [gr_adj, eb], by simp [h1]⟩
  | c1 => exact absurd rfl hx
  | wa _ => exact ⟨c1, by simp [gr_adj, eb], by simp [h1]⟩
  | ru ν => exact ⟨c2, by simp [gr_adj, eb], by simp [h1]⟩
  | rl μ => exact ⟨ll μ, by simp [gr_adj, eb], by simp [h1]⟩
  | tb μ j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := tb_step a b μ j <;>
      exact ⟨_, hy, by simp [h1] <;> omega⟩
  | c2 => exact ⟨c0, by simp [gr_adj, eb], by simp [h1]⟩
  | c3 => exact ⟨c2, by simp [gr_adj, eb], by simp [h1]⟩
  | wb _ => exact ⟨c2, by simp [gr_adj, eb], by simp [h1]⟩

lemma edist_c2 (x : DV k p fa fb) : (gr a b).edist x c2 ≤ h2 x := by
  refine edist_le_of_descent _ _ (fun x hx => ?_) x
  cases x with
  | lu ν => exact ⟨ru ν, by simp [gr_adj, eb], by simp [h2]⟩
  | ll μ => exact ⟨c1, by simp [gr_adj, eb], by simp [h2]⟩
  | ta ν j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := ta_step a b ν j <;>
      exact ⟨_, hy, by simp [h2] <;> omega⟩
  | c0 => exact ⟨c2, by simp [gr_adj, eb], by simp [h2]⟩
  | c1 => exact ⟨c0, by simp [gr_adj, eb], by simp [h2]⟩
  | wa _ => exact ⟨c0, by simp [gr_adj, eb], by simp [h2]⟩
  | ru ν => exact ⟨c2, by simp [gr_adj, eb], by simp [h2]⟩
  | rl μ => exact ⟨c3, by simp [gr_adj, eb], by simp [h2]⟩
  | tb μ j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := tb_step a b μ j <;>
      exact ⟨_, hy, by simp [h2] <;> omega⟩
  | c2 => exact absurd rfl hx
  | c3 => exact ⟨c2, by simp [gr_adj, eb], by simp [h2]⟩
  | wb _ => exact ⟨c2, by simp [gr_adj, eb], by simp [h2]⟩

lemma edist_c3 (x : DV k p fa fb) : (gr a b).edist x c3 ≤ h3 x := by
  refine edist_le_of_descent _ _ (fun x hx => ?_) x
  cases x with
  | lu ν => exact ⟨ru ν, by simp [gr_adj, eb], by simp [h3]⟩
  | ll μ => exact ⟨rl μ, by simp [gr_adj, eb], by simp [h3]⟩
  | ta ν j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := ta_step a b ν j <;>
      exact ⟨_, hy, by simp [h3] <;> omega⟩
  | c0 => exact ⟨c2, by simp [gr_adj, eb], by simp [h3]⟩
  | c1 => exact ⟨c0, by simp [gr_adj, eb], by simp [h3]⟩
  | wa _ => exact ⟨c0, by simp [gr_adj, eb], by simp [h3]⟩
  | ru ν => exact ⟨c2, by simp [gr_adj, eb], by simp [h3]⟩
  | rl μ => exact ⟨c3, by simp [gr_adj, eb], by simp [h3]⟩
  | tb μ j =>
    obtain ⟨y, hy, ⟨hj, rfl⟩ | ⟨j', hj', rfl⟩⟩ := tb_step a b μ j <;>
      exact ⟨_, hy, by simp [h3] <;> omega⟩
  | c2 => exact ⟨c3, by simp [gr_adj, eb], by simp [h3]⟩
  | c3 => exact absurd rfl hx
  | wb _ => exact ⟨c3, by simp [gr_adj, eb], by simp [h3]⟩

lemma edist_le_of_hub (u v : DV k p fa fb) (n : ℕ)
    (h : h0 u + h0 v ≤ n ∨ h1 u + h1 v ≤ n ∨ h2 u + h2 v ≤ n ∨ h3 u + h3 v ≤ n) :
    (gr a b).edist u v ≤ n := by
  have key : ∀ t : DV k p fa fb, ∀ m₁ m₂ : ℕ, (gr a b).edist u t ≤ m₁ →
      (gr a b).edist v t ≤ m₂ → m₁ + m₂ ≤ n → (gr a b).edist u v ≤ n := by
    intro t m₁ m₂ h₁ h₂ hm
    calc (gr a b).edist u v ≤ (gr a b).edist u t + (gr a b).edist t v := SimpleGraph.edist_triangle
      _ ≤ m₁ + m₂ := by rw [edist_comm (u := t)]; exact add_le_add h₁ h₂
      _ ≤ n := by exact_mod_cast hm
  rcases h with h | h | h | h
  · exact key _ _ _ (edist_c0 a b u) (edist_c0 a b v) h
  · exact key _ _ _ (edist_c1 a b u) (edist_c1 a b v) h
  · exact key _ _ _ (edist_c2 a b u) (edist_c2 a b v) h
  · exact key _ _ _ (edist_c3 a b u) (edist_c3 a b v) h

lemma edist_ta_lu (ν : Fin k) (j : Fin p) :
    (gr (p := p) (fa := fa) (fb := fb) a b).edist (ta ν j) (lu ν) ≤ (j.val + 1 : ℕ) := by
  induction h : j.val generalizing j with
  | zero =>
    have hj : j.val = 0 := h
    exact (edist_le_one_iff_adj_or_eq.2 (Or.inl (by simp [gr_adj, eb, hj]))).trans (by simp)
  | succ n ih =>
    have h' := ih ⟨n, by omega⟩ rfl
    have hadj : (gr (p := p) (fa := fa) (fb := fb) a b).Adj (ta ν j) (ta ν ⟨n, by omega⟩) := by
      simp [gr_adj, eb]; omega
    calc _ ≤ (gr (p := p) (fa := fa) (fb := fb) a b).edist (ta ν j) (ta ν ⟨n, by omega⟩) +
          (gr (p := p) (fa := fa) (fb := fb) a b).edist (ta ν ⟨n, by omega⟩) (lu ν) :=
            SimpleGraph.edist_triangle
      _ ≤ 1 + ((n + 1 : ℕ) : ℕ∞) := add_le_add (edist_eq_one_iff_adj.2 hadj).le h'
      _ = ((n + 1 + 1 : ℕ) : ℕ∞) := by push_cast; ring

lemma edist_tb_rl (μ : Fin k) (j : Fin p) :
    (gr (p := p) (fa := fa) (fb := fb) a b).edist (tb μ j) (rl μ) ≤ (j.val + 1 : ℕ) := by
  induction h : j.val generalizing j with
  | zero =>
    have hj : j.val = 0 := h
    exact (edist_le_one_iff_adj_or_eq.2 (Or.inl (by simp [gr_adj, eb, hj]))).trans (by simp)
  | succ n ih =>
    have h' := ih ⟨n, by omega⟩ rfl
    have hadj : (gr (p := p) (fa := fa) (fb := fb) a b).Adj (tb μ j) (tb μ ⟨n, by omega⟩) := by
      simp [gr_adj, eb]; omega
    calc _ ≤ (gr (p := p) (fa := fa) (fb := fb) a b).edist (tb μ j) (tb μ ⟨n, by omega⟩) +
          (gr (p := p) (fa := fa) (fb := fb) a b).edist (tb μ ⟨n, by omega⟩) (rl μ) :=
            SimpleGraph.edist_triangle
      _ ≤ 1 + ((n + 1 : ℕ) : ℕ∞) := add_le_add (edist_eq_one_iff_adj.2 hadj).le h'
      _ = ((n + 1 + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- If `a` and `b` do not share the bit `(ν, μ)`, then `d(l_ν, r_μ) ≤ 2`. -/
lemma edist_lu_rl (ν μ : Fin k) (h : ¬(a (ν, μ) = true ∧ b (ν, μ) = true)) :
    (gr (p := p) (fa := fa) (fb := fb) a b).edist (lu ν) (rl μ) ≤ 2 := by
  have two : ∀ y, (gr (p := p) (fa := fa) (fb := fb) a b).Adj (lu ν) y →
      (gr (p := p) (fa := fa) (fb := fb) a b).Adj y (rl μ) →
      (gr (p := p) (fa := fa) (fb := fb) a b).edist (lu ν) (rl μ) ≤ 2 := by
    intro y h1 h2
    calc _ ≤ _ := SimpleGraph.edist_triangle (v := y)
      _ ≤ 1 + 1 := add_le_add (edist_eq_one_iff_adj.2 h1).le (edist_eq_one_iff_adj.2 h2).le
      _ = 2 := by norm_num
  cases ha : a (ν, μ)
  · exact two (ll μ) (by simp [gr_adj, eb, ha]) (by simp [gr_adj, eb])
  · have hb : b (ν, μ) = false := by simpa [ha] using h
    exact two (ru ν) (by simp [gr_adj, eb]) (by simp [gr_adj, eb, hb])

/-- Anchored bound: `d(u, v) ≤ d(u, l_ν) + 2 + d(r_μ, v)` when the bit `(ν, μ)` is not shared. -/
lemma edist_anchor {ν μ : Fin k} (h : ¬(a (ν, μ) = true ∧ b (ν, μ) = true)) (u v : DV k p fa fb)
    (m₁ m₂ : ℕ) (hu : (gr a b).edist u (lu ν) ≤ m₁) (hv : (gr a b).edist v (rl μ) ≤ m₂) :
    (gr a b).edist u v ≤ (m₁ + 2 + m₂ : ℕ) := by
  calc (gr a b).edist u v ≤ (gr a b).edist u (lu ν) + (gr a b).edist (lu ν) v :=
        SimpleGraph.edist_triangle
    _ ≤ (gr a b).edist u (lu ν) + ((gr a b).edist (lu ν) (rl μ) + (gr a b).edist (rl μ) v) :=
        add_le_add le_rfl SimpleGraph.edist_triangle
    _ ≤ m₁ + (2 + m₂) := by
        rw [edist_comm (u := rl μ)]
        exact add_le_add hu (add_le_add (edist_lu_rl a b ν μ h) hv)
    _ = _ := by push_cast; ring

/-- Every distance in `G_{a,b}` is at most `2p + 4 = d + 2` (upper half of Lemma 8). -/
theorem edist_le_two_mul_add_four (hp : 1 ≤ p) (u v : DV k p fa fb) :
    (gr a b).edist u v ≤ (2 * p + 4 : ℕ) := by
  apply edist_le_of_hub
  cases u <;> cases v <;> simp only [h0, h1, h2, h3] <;> omega

/-- **Claim 2** of [HW12]: the nodes `c₀, c₁, c₂, c₃` and the fill-up nodes have distance at most
`2p + 2 = d` to every node. -/
theorem claim2 (hp : 1 ≤ p) (u v : DV k p fa fb)
    (hu : u = c0 ∨ u = c1 ∨ u = c2 ∨ u = c3 ∨ (∃ j, u = wa j) ∨ ∃ j, u = wb j) :
    (gr a b).edist u v ≤ (2 * p + 2 : ℕ) := by
  apply edist_le_of_hub
  rcases hu with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    cases v <;> simp only [h0, h1, h2, h3] <;> omega

/-- If `a` and `b` are disjoint, every distance in `G_{a,b}` is at most `2p + 2 = d`
(upper half of Lemma 9). -/
theorem edist_le_of_disj (hp : 1 ≤ p) (hd : ∀ i, ¬(a i = true ∧ b i = true))
    (u v : DV k p fa fb) : (gr a b).edist u v ≤ (2 * p + 2 : ℕ) := by
  have A : ∀ ν μ (u v : DV k p fa fb) (m₁ m₂ : ℕ), (gr a b).edist u (lu ν) ≤ m₁ →
      (gr a b).edist v (rl μ) ≤ m₂ → m₁ + 2 + m₂ ≤ 2 * p + 2 →
      (gr a b).edist u v ≤ (2 * p + 2 : ℕ) ∧ (gr a b).edist v u ≤ (2 * p + 2 : ℕ) := by
    intro ν μ u v m₁ m₂ h₁ h₂ hm
    have := (edist_anchor a b (hd (ν, μ)) u v m₁ m₂ h₁ h₂).trans
      (by exact_mod_cast hm : ((m₁ + 2 + m₂ : ℕ) : ℕ∞) ≤ ((2 * p + 2 : ℕ) : ℕ∞))
    exact ⟨this, by rwa [edist_comm]⟩
  have l0 : ∀ ν, (gr (p := p) (fa := fa) (fb := fb) a b).edist (lu ν) (lu ν) ≤ (0 : ℕ) := by simp
  have r0 : ∀ μ, (gr (p := p) (fa := fa) (fb := fb) a b).edist (rl μ) (rl μ) ≤ (0 : ℕ) := by simp
  cases u <;> cases v
  all_goals first
    | (apply edist_le_of_hub; simp only [h0, h1, h2, h3]; omega)
    | exact (A _ _ _ _ _ _ (l0 _) (r0 _) (by omega)).1
    | exact (A _ _ _ _ _ _ (l0 _) (r0 _) (by omega)).2
    | exact (A _ _ _ _ _ _ (l0 _) (edist_tb_rl a b _ _) (by omega)).1
    | exact (A _ _ _ _ _ _ (l0 _) (edist_tb_rl a b _ _) (by omega)).2
    | exact (A _ _ _ _ _ _ (edist_ta_lu a b _ _) (r0 _) (by omega)).1
    | exact (A _ _ _ _ _ _ (edist_ta_lu a b _ _) (r0 _) (by omega)).2
    | exact (A _ _ _ _ _ _ (edist_ta_lu a b _ _) (edist_tb_rl a b _ _) (by omega)).1
    | exact (A _ _ _ _ _ _ (edist_ta_lu a b _ _) (edist_tb_rl a b _ _) (by omega)).2

end Upper


/-! ### Lower bounds on distances: Lipschitz potentials -/

section Lower

variable (a b : Fin k × Fin k → Bool)

lemma lipschitz_of_eb (f : DV k p fa fb → ℕ)
    (hf : ∀ x y, eb a b x y = true → f y ≤ f x + 1 ∧ f x ≤ f y + 1) :
    ∀ x y, (gr a b).Adj x y → f y ≤ f x + 1 := by
  rintro x y (h | h)
  · exact (hf x y h).1
  · exact (hf y x h).2

/-- The last node `l'_ν` (resp. `r'_μ`) of a path `T^a_ν` (resp. `T^b_μ`). -/
def last (hp : 1 ≤ p) : Fin p := ⟨p - 1, by omega⟩

/-- Potential for `d(l'_ν, r'_μ) ≥ 2p + 2`. -/
def pot1 (ν μ : Fin k) : DV k p fa fb → ℕ
  | ta ν' j => if ν' = ν then p - 1 - j.val else p + 1
  | lu ν' => if ν' = ν then p else p + 1
  | rl μ' => if μ' = μ then p + 2 else p + 1
  | tb μ' j => if μ' = μ then p + 3 + j.val else p + 1
  | _ => p + 1

/-- Potential for `d(l'_ν, r'_μ) ≥ 2p + 4` when `a (ν, μ) = b (ν, μ) = 1`. -/
def pot2 (ν μ : Fin k) : DV k p fa fb → ℕ
  | ta ν' j => if ν' = ν then p - 1 - j.val else p + 2
  | lu ν' => if ν' = ν then p else p + 2
  | c0 => p + 1
  | wa _ => p + 1
  | c1 => p + 2
  | ll μ' => if μ' = μ then p + 3 else p + 1
  | ru ν' => if ν' = ν then p + 1 else p + 3
  | c2 => p + 2
  | wb _ => p + 2
  | c3 => p + 3
  | rl μ' => if μ' = μ then p + 4 else p + 2
  | tb μ' j => if μ' = μ then p + 5 + j.val else p + 2

/-- `d(l'_ν, r'_μ) ≥ 2p + 2 = d` for all `ν`, `μ` (lower half of Lemma 9). -/
theorem le_edist_last (hp : 1 ≤ p) (ν μ : Fin k) :
    ((2 * p + 2 : ℕ) : ℕ∞) ≤ 
      (gr (p := p) (fa := fa) (fb := fb) a b).edist (ta ν (last hp)) (tb μ (last hp)) := by
  have hf := le_edist_of_lipschitz (pot1 (fa := fa) (fb := fb) ν μ) 
    (lipschitz_of_eb a b _ fun x y h => by
      cases x <;> cases y <;> simp [eb] at h <;> simp only [pot1] <;> (try split_ifs) <;>
        subst_vars <;> simp_all <;> omega) (ta ν (last hp)) (tb μ (last hp))
  have e : pot1 (fa := fa) (fb := fb) ν μ (tb μ (last hp)) -
      pot1 (fa := fa) (fb := fb) ν μ (ta ν (last hp)) =
      2 * p + 2 := by
    simp [pot1, last]; omega
  rwa [e] at hf

/-- If `a (ν, μ) = b (ν, μ) = 1` then `d(l'_ν, r'_μ) ≥ 2p + 4 = d + 2` (Lemma 8). -/
theorem le_edist_last_of_inter (hp : 1 ≤ p) (ν μ : Fin k) (ha : a (ν, μ) = true)
    (hb : b (ν, μ) = true) :
    ((2 * p + 4 : ℕ) : ℕ∞) ≤ 
      (gr (p := p) (fa := fa) (fb := fb) a b).edist (ta ν (last hp)) (tb μ (last hp)) := by
  have hf := le_edist_of_lipschitz (pot2 (fa := fa) (fb := fb) ν μ) 
    (lipschitz_of_eb a b _ fun x y h => by
      cases x <;> cases y <;> simp [eb] at h <;> simp only [pot2] <;> (try split_ifs) <;>
        subst_vars <;> simp_all <;> omega) (ta ν (last hp)) (tb μ (last hp))
  have e : pot2 (fa := fa) (fb := fb) ν μ (tb μ (last hp)) -
      pot2 (fa := fa) (fb := fb) ν μ (ta ν (last hp)) =
      2 * p + 4 := by
    simp [pot2, last]; omega
  rwa [e] at hf

end Lower

/-! ### Lemmas 8 and 9 -/

section Diam

variable (a b : Fin k × Fin k → Bool)

instance : Nonempty (DV k p fa fb) := ⟨c0⟩

lemma disj_eq_true_iff {ι : Type*} [Fintype ι] {x y : ι → Bool} :
    disj x y = true ↔ ∀ i, ¬(x i = true ∧ y i = true) := by
  simp [disj]

lemma ediam_le (hp : 1 ≤ p) : (gr (p := p) (fa := fa) (fb := fb) a b).ediam ≤ (2 * p + 4 : ℕ) :=
  ediam_le_iff.2 (edist_le_two_mul_add_four a b hp)

/-- `G_{a,b}` is connected. -/
theorem gr_connected (hp : 1 ≤ p) : (gr (p := p) (fa := fa) (fb := fb) a b).Connected :=
  connected_of_ediam_ne_top (ne_top_of_le_ne_top (ENat.natCast_ne_top _) (ediam_le a b hp))

lemma diam_eq_of_ediam_eq {n : ℕ} (h : (gr (p := p) (fa := fa) (fb := fb) a b).ediam = n) :
    (gr (p := p) (fa := fa) (fb := fb) a b).diam = n := by
  simp [SimpleGraph.diam, h]

/-- **Lemma 8** of [HW12]: if `a` and `b` are not disjoint, the diameter of `G_{a,b}` is
`d + 2 = 2p + 4`. -/
theorem lemma8 (hp : 1 ≤ p) (h : disj a b = false) :
    (gr (p := p) (fa := fa) (fb := fb) a b).ediam = (2 * p + 4 : ℕ) ∧
      (gr (p := p) (fa := fa) (fb := fb) a b).diam = 2 * p + 4 := by
  obtain ⟨⟨ν, μ⟩, ha, hb⟩ : ∃ i, a i = true ∧ b i = true := by simpa [disj] using h
  have e : (gr (p := p) (fa := fa) (fb := fb) a b).ediam = (2 * p + 4 : ℕ) :=
    le_antisymm (ediam_le a b hp) ((le_edist_last_of_inter a b hp ν μ ha hb).trans edist_le_ediam)
  exact ⟨e, diam_eq_of_ediam_eq a b e⟩

/-- If `a` and `b` are disjoint, the diameter of `G_{a,b}` is `d = 2p + 2` (needs `k ≥ 1`). -/
theorem ediam_eq_of_disj (hp : 1 ≤ p) (hk : 1 ≤ k) (h : disj a b = true) :
    (gr (p := p) (fa := fa) (fb := fb) a b).ediam = (2 * p + 2 : ℕ) :=
  le_antisymm (ediam_le_iff.2 (edist_le_of_disj a b hp (disj_eq_true_iff.1 h)))
    ((le_edist_last a b hp ⟨0, hk⟩ ⟨0, hk⟩).trans edist_le_ediam)

/-- **Lemma 9** of [HW12]: `a` and `b` are disjoint iff the diameter of `G_{a,b}` is `d = 2p + 2`.
-/
theorem lemma9 (hp : 1 ≤ p) (hk : 1 ≤ k) :
    disj a b = true ↔ (gr (p := p) (fa := fa) (fb := fb) a b).diam = 2 * p + 2 := by
  constructor
  · exact fun h => diam_eq_of_ediam_eq a b (ediam_eq_of_disj a b hp hk h)
  · intro h
    by_contra h'
    have := (lemma8 (fa := fa) (fb := fb) a b hp (by simpa using h')).2
    omega

/-- The diameter of `G_{a,b}` is `d = 2p + 2` or `d + 2 = 2p + 4`. -/
theorem diam_mem (hp : 1 ≤ p) (hk : 1 ≤ k) :
    (gr (p := p) (fa := fa) (fb := fb) a b).diam = 2 * p + 2 ∨
      (gr (p := p) (fa := fa) (fb := fb) a b).diam = 2 * p + 4 := by
  cases h : disj a b
  · exact Or.inr (lemma8 a b hp h).2
  · exact Or.inl ((lemma9 a b hp hk).1 h)

end Diam

/-! ### Counting the vertices -/

section Card

/-- `DV` as a sum type (Alice's part, Bob's part). -/
def DV.equivSum : DV k p fa fb ≃ (Fin k ⊕ Fin k ⊕ (Fin k × Fin p) ⊕ Bool ⊕ Fin fa) ⊕
    (Fin k ⊕ Fin k ⊕ (Fin k × Fin p) ⊕ Bool ⊕ Fin fb) where
  toFun
    | lu ν => .inl (.inl ν)
    | ll μ => .inl (.inr (.inl μ))
    | ta ν j => .inl (.inr (.inr (.inl (ν, j))))
    | c0 => .inl (.inr (.inr (.inr (.inl false))))
    | c1 => .inl (.inr (.inr (.inr (.inl true))))
    | wa j => .inl (.inr (.inr (.inr (.inr j))))
    | ru ν => .inr (.inl ν)
    | rl μ => .inr (.inr (.inl μ))
    | tb μ j => .inr (.inr (.inr (.inl (μ, j))))
    | c2 => .inr (.inr (.inr (.inr (.inl false))))
    | c3 => .inr (.inr (.inr (.inr (.inl true))))
    | wb j => .inr (.inr (.inr (.inr (.inr j))))
  invFun
    | .inl (.inl ν) => lu ν
    | .inl (.inr (.inl μ)) => ll μ
    | .inl (.inr (.inr (.inl (ν, j)))) => ta ν j
    | .inl (.inr (.inr (.inr (.inl false)))) => c0
    | .inl (.inr (.inr (.inr (.inl true)))) => c1
    | .inl (.inr (.inr (.inr (.inr j)))) => wa j
    | .inr (.inl ν) => ru ν
    | .inr (.inr (.inl μ)) => rl μ
    | .inr (.inr (.inr (.inl (μ, j)))) => tb μ j
    | .inr (.inr (.inr (.inr (.inl false)))) => c2
    | .inr (.inr (.inr (.inr (.inl true)))) => c3
    | .inr (.inr (.inr (.inr (.inr j)))) => wb j
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with (x | x | ⟨x, y⟩ | x | x) | (x | x | ⟨x, y⟩ | x | x) <;> (try cases x) <;> rfl

instance : Fintype (DV k p fa fb) := Fintype.ofEquiv _ DV.equivSum.symm

/-- `|V(G_{a,b})| = 2 (k (p + 2) + 2) + f_a + f_b`. -/
lemma DV.card : Fintype.card (DV k p fa fb) = 2 * (k * (p + 2) + 2) + fa + fb := by
  rw [Fintype.card_congr DV.equivSum]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

end Card

/-! ### The family of lower-bound graphs -/

section Family

open Finset

/-- Alice's vertices: `L`, `L'`, the paths `T^a_ν`, `c₀`, `c₁` and her fill-up nodes. -/
def DV.alice : DV k p fa fb → Bool
  | lu _ | ll _ | ta _ _ | c0 | c1 | wa _ => true
  | _ => false

/-- The cut edges `(l_i, r_i)`, `i < 2k`, and `(c₀, c₂)`. -/
def cutDV : Finset (DV k p fa fb × DV k p fa fb) :=
  (univ.image fun ν => (lu ν, ru ν)) ∪ (univ.image fun μ => (ll μ, rl μ)) ∪ {(c0, c2)}

lemma card_cutDV : (cutDV (k := k) (p := p) (fa := fa) (fb := fb)).card ≤ 2 * k + 1 := by
  unfold cutDV
  have h0 := card_union_le ((univ.image fun ν => ((lu ν : DV k p fa fb), (ru ν : DV k p fa fb))) ∪
    (univ.image fun μ => ((ll μ : DV k p fa fb), (rl μ : DV k p fa fb)))) {(c0, c2)}
  have h0' := card_union_le (univ.image fun ν => ((lu ν : DV k p fa fb), (ru ν : DV k p fa fb)))
    (univ.image fun μ => ((ll μ : DV k p fa fb), (rl μ : DV k p fa fb)))
  have h1 := card_image_le (s := (univ : Finset (Fin k)))
    (f := fun ν => ((lu ν : DV k p fa fb), (ru ν : DV k p fa fb)))
  have h2 := card_image_le (s := (univ : Finset (Fin k)))
    (f := fun μ => ((ll μ : DV k p fa fb), (rl μ : DV k p fa fb)))
  simp only [card_univ, Fintype.card_fin, card_singleton] at h0 h1 h2 ⊢
  omega

variable (a b a' b' : Fin k × Fin k → Bool)

lemma cut_sub (q : DV k p fa fb × DV k p fa fb) (hq : q ∈ cutDV) :
    DV.alice q.1 = true ∧ DV.alice q.2 = false := by
  simp only [cutDV, mem_union, mem_image, mem_univ, true_and, mem_singleton] at hq
  rcases hq with (⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl <;> simp [DV.alice]

lemma adj_cut (x y : DV k p fa fb) (hx : DV.alice x = true) (hy : DV.alice y = false)
    (h : (gr a b).Adj x y) : (x, y) ∈ cutDV := by
  simp only [cutDV, mem_union, mem_image, mem_univ, true_and, mem_singleton]
  cases x <;> cases y <;> simp_all [DV.alice, gr_adj, eb]

lemma adj_alice (x y : DV k p fa fb) (hx : DV.alice x = true) (hy : DV.alice y = true) :
    (gr a b).Adj x y ↔ (gr a b').Adj x y := by
  cases x <;> cases y <;> simp_all [DV.alice, gr_adj, eb]

lemma adj_bob (x y : DV k p fa fb) (hx : DV.alice x = false) (hy : DV.alice y = false) :
    (gr a b).Adj x y ↔ (gr a' b).Adj x y := by
  cases x <;> cases y <;> simp_all [DV.alice, gr_adj, eb]

lemma adj_fixed (x y : DV k p fa fb) (hx : DV.alice x = true) (hy : DV.alice y = false) :
    (gr a b).Adj x y ↔ (gr a' b').Adj x y := by
  cases x <;> cases y <;> simp_all [DV.alice, gr_adj, eb]

variable {V : Type*} (e : V ≃ DV k p fa fb)

instance : DecidableRel ((gr a b).comap e).Adj := fun u v =>
  inferInstanceAs (Decidable ((gr a b).Adj (e u) (e v)))

/-- The family of lower-bound graphs of Theorem 4, relabelled to the vertex set `V` along `e`;
node inputs are the adjacency rows. -/
def fam : LBFamily (Fin k × Fin k → Bool) (Fin k × Fin k → Bool) V (V → Bool) :=
  LBFamily.ofAdj (fun a b => (gr a b).comap e) (fun v => DV.alice (e v))
    (cutDV.map (e.symm.prodCongr e.symm).toEmbedding)
    (fun q hq => by
      rw [mem_map_equiv] at hq
      simpa using cut_sub _ hq)
    (fun a b u v hu hv h => by
      rw [mem_map_equiv]
      simpa using adj_cut a b (e u) (e v) hu hv h)
    (fun a b b' u v hu hv => adj_alice a b b' (e u) (e v) hu hv)
    (fun a a' b u v hu hv => adj_bob a b a' (e u) (e v) hu hv)
    (fun a a' b b' u v hu hv => adj_fixed a b a' b' (e u) (e v) hu hv)

instance : DecidableRel ((fam e).G a b).Adj :=
  inferInstanceAs (DecidableRel ((gr a b).comap e).Adj)

lemma fam_G : (fam e).G a b = (gr a b).comap e := rfl

lemma fam_card : (fam e).Ecut.card ≤ 2 * k + 1 := by
  simp only [fam, LBFamily.ofAdj, card_map]
  exact card_cutDV

end Family

/-! ### Facts about the relabelled graphs -/

section Relabelled

variable {V : Type*} (e : V ≃ DV k p fa fb) (a b : Fin k × Fin k → Bool)

lemma comap_ediam : ((gr a b).comap e).ediam = (gr (p := p) (fa := fa) (fb := fb) a b).ediam :=
  ediam_comap_equiv _ e

lemma comap_diam : ((gr a b).comap e).diam = (gr (p := p) (fa := fa) (fb := fb) a b).diam := by
  simp only [SimpleGraph.diam, comap_ediam e]

lemma comap_connected (hp : 1 ≤ p) : ((gr a b).comap e).Connected := by
  have : Nonempty V := ⟨e.symm c0⟩
  refine connected_of_ediam_ne_top ?_
  rw [comap_ediam]
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (ediam_le a b hp)

lemma comap_diam_mem (hp : 1 ≤ p) (hk : 1 ≤ k) :
    ((gr a b).comap e).diam = 2 * p + 2 ∨ ((gr a b).comap e).diam = 2 * p + 2 + 2 := by
  rw [comap_diam]
  have := diam_mem (fa := fa) (fb := fb) a b hp hk
  omega

/-- In the relabelled graph of intersecting inputs, two nodes are at distance `≥ d + 2`. -/
lemma comap_far (hp : 1 ≤ p) (h : disj a b = false) :
    ∃ u v : V, ((2 * p + 4 : ℕ) : ℕ∞) ≤ ((gr a b).comap e).edist u v := by
  obtain ⟨⟨ν, μ⟩, ha, hb⟩ : ∃ i, a i = true ∧ b i = true := by simpa [disj] using h
  refine ⟨e.symm (ta ν (last hp)), e.symm (tb μ (last hp)), ?_⟩
  rw [edist_comap_equiv, e.apply_symm_apply, e.apply_symm_apply]
  exact le_edist_last_of_inter a b hp ν μ ha hb

end Relabelled

/-! ### From a decision rule to the lower bound -/

section Reduction

variable {V I σ : Type*} {B : ℕ}

-- CSLib candidate (`Algorithm.withOut`, `withOut_run`)
/-- The algorithm `A` with the output function replaced by `o` (same states, same messages). -/
def withOut (A : Algorithm V I σ B) (o : V → σ → Bool) : Algorithm V I σ B := { A with out := o }

lemma withOut_run (A : Algorithm V I σ B) (o : V → σ → Bool) (G : SimpleGraph V)
    [DecidableRel G.Adj] (inp : V → I) : ∀ t, (withOut A o).run G inp t = A.run G inp t
  | 0 => rfl
  | t + 1 => by
      funext v
      simp only [Algorithm.run, withOut_run A o G inp t]
      rfl

/-- The states after `T` rounds on `G_{a,b}` relabelled along `e`, with adjacency rows as inputs. -/
abbrev runOn (A : Algorithm V (V → Bool) σ B) (e : V ≃ DV k p fa fb) (a b : Fin k × Fin k → Bool)
    (T : ℕ) : V → σ :=
  A.run ((gr a b).comap e) (fun v w => decide (((gr a b).comap e).Adj v w)) T

/-- The core reduction (the proof of Theorem 4 via Theorem 3 of [HW12], i.e. the simulation
theorem of CSLib with `|C| ≤ 2k + 1` cut edges and the deterministic `CC(DISJ_{k²}) ≥ k²`): if a
node-local rule `o` lets all nodes accept on disjoint inputs and some node reject on intersecting
ones, then `k² ≤ T · 2 (2k + 1) B + 2`. -/
theorem lowerBound_of_rule [Finite V] (e : V ≃ DV k p fa fb) (A : Algorithm V (V → Bool) σ B)
    (o : V → σ → Bool) (T : ℕ)
    (hyes : ∀ a b, disj a b = true → ∀ v, o v (runOn A e a b T v) = true)
    (hno : ∀ a b, disj a b = false → ∃ v, o v (runOn A e a b T v) = false) :
    k * k ≤ T * (2 * ((2 * k + 1) * B)) + 2 := by
  have h := (fam e).disj_lowerBound (withOut A o) T (fun a b => by
    simp only [Algorithm.Accepts, withOut_run]
    change (∀ v, o v (runOn A e a b T v) = true) ↔ _
    cases h : disj a b
    · obtain ⟨v, hv⟩ := hno a b h
      simp only [Bool.false_eq_true, iff_false, not_forall]
      exact ⟨v, by simp [hv]⟩
    · simpa using hyes a b h)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  refine h.trans ?_
  have := fam_card e
  gcongr

end Reduction

/-! ### Theorem 4 and Lemma 10 -/

section Main

variable {V σ : Type*} [Fintype V] {n d B T : ℕ}

/-- The parameters of the proof of Theorem 4: `d = 2p + 2`, `k = ⌊(n - 4)/(d + 2)⌋ ≥ 1`, and the
fill-up counts `f_a + f_b = n - 2 (k (p + 2) + 2)` (`f_a = ⌊·/2⌋`, `f_b = ⌈·/2⌉`). -/
lemma setup (hV : Fintype.card V = n) (hd : 4 ≤ d) (hev : Even d) (hn : d + 6 ≤ n) :
    ∃ p fa fb : ℕ, d = 2 * p + 2 ∧ 1 ≤ p ∧ 1 ≤ (n - 4) / (d + 2) ∧
      Nonempty (V ≃ DV ((n - 4) / (d + 2)) p fa fb) := by
  obtain ⟨q, rfl⟩ := hev
  set k := (n - 4) / (q + q + 2) with hk
  have hk1 : 1 ≤ k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hk2 : k * (q + q + 2) ≤ n - 4 := Nat.div_mul_le_self _ _
  set r := n - 2 * (k * (q - 1 + 2) + 2)
  refine ⟨q - 1, r / 2, r - r / 2, by omega, by omega, hk1, ⟨Fintype.equivOfCardEq ?_⟩⟩
  rw [DV.card, hV]
  have : k * (q - 1 + 2) * 2 = k * (q + q + 2) := by
    rw [mul_assoc]; congr 1; omega
  omega

/-- **Theorem 4** of [HW12] (deterministic version). Let `d ≥ 4` be even, `n ≥ d + 6`, and let
`A` be a deterministic CONGEST algorithm with `B`-bit messages on the `n` node IDs `V` (node
input: its adjacency row) that, on every connected graph of diameter `d` or `d + 2`, outputs at
every node after `T` rounds a `(+,1)`-approximation `est` of the diameter
(`D ≤ est ≤ D + 1`). Then, with `k = ⌊(n - 4)/(d + 2)⌋`,
`k² ≤ T · 2 (2k + 1) B + 2`; hence `T = Ω(k / B) = Ω(n / (D B))` (see `theorem4_bound`). -/
theorem theorem4 (hV : Fintype.card V = n) (hd : 4 ≤ d) (hev : Even d) (hn : d + 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (est : V → σ → ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (G.diam = d ∨ G.diam = d + 2) → ∀ v,
        G.diam ≤ est v (A.run G (fun v w => decide (G.Adj v w)) T v) ∧
          est v (A.run G (fun v w => decide (G.Adj v w)) T v) ≤ G.diam + 1) :
    (n - 4) / (d + 2) * ((n - 4) / (d + 2)) ≤
      T * (2 * ((2 * ((n - 4) / (d + 2)) + 1) * B)) + 2 := by
  obtain ⟨p, fa, fb, rfl, hp, hk, ⟨e⟩⟩ := setup hV hd hev hn
  refine lowerBound_of_rule e A (fun v s => decide (est v s < 2 * p + 2 + 2)) T
    (fun a b h v => ?_) (fun a b h => ⟨e.symm c0, ?_⟩)
  · have hdiam : ((gr a b).comap e).diam = 2 * p + 2 := by
      rw [comap_diam]; exact (lemma9 a b hp hk).1 h
    have := (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk) v).2
    simp only [runOn, decide_eq_true_eq]
    omega
  · have hdiam : ((gr a b).comap e).diam = 2 * p + 4 := by
      rw [comap_diam]; exact (lemma8 a b hp h).2
    have := (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk) (e.symm c0)).1
    simp only [runOn, decide_eq_false_iff_not, not_lt]
    omega

/-- The round bound of Theorem 4 in closed form: `⌊(n - 4)/(d + 2)⌋ ≤ 4 T B + 2`, i.e.
`T ≥ (⌊(n - 4)/(d + 2)⌋ - 2) / (4B) = Ω(n / (D · B))`. -/
theorem theorem4_bound (hV : Fintype.card V = n) (hd : 4 ≤ d) (hev : Even d) (hn : d + 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (est : V → σ → ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (G.diam = d ∨ G.diam = d + 2) → ∀ v,
        G.diam ≤ est v (A.run G (fun v w => decide (G.Adj v w)) T v) ∧
          est v (A.run G (fun v w => decide (G.Adj v w)) T v) ≤ G.diam + 1) :
    (n - 4) / (d + 2) ≤ 4 * T * B + 2 := by
  have h := theorem4 hV hd hev hn A est hA
  set k := (n - 4) / (d + 2)
  by_contra hc
  have h1 : 4 * (T * B) + 3 ≤ k := by rw [← mul_assoc]; omega
  have h2 : T * (2 * ((2 * k + 1) * B)) = (4 * k + 2) * (T * B) := by ring
  rw [h2] at h
  nlinarith

/-- **Lemma 10** of [HW12], `(+,1)`-eccentricity part: if every node outputs a `(+,1)`-estimate
`est` of its own eccentricity (`ecc(v) ≤ est ≤ ecc(v) + 1`) on every connected graph of diameter
`d` or `d + 2`, the bound of Theorem 4 holds. (No aggregation is needed: in the decision version a
node rejects iff its estimate is `≥ d + 2`.) -/
theorem lemma10_eccent_plusOne (hV : Fintype.card V = n) (hd : 4 ≤ d) (hev : Even d) (hn : d + 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (est : V → σ → ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (G.diam = d ∨ G.diam = d + 2) → ∀ v,
        G.eccent v ≤ est v (A.run G (fun v w => decide (G.Adj v w)) T v) ∧
          (est v (A.run G (fun v w => decide (G.Adj v w)) T v) : ℕ∞) ≤ G.eccent v + 1) :
    (n - 4) / (d + 2) * ((n - 4) / (d + 2)) ≤
      T * (2 * ((2 * ((n - 4) / (d + 2)) + 1) * B)) + 2 := by
  obtain ⟨p, fa, fb, rfl, hp, hk, ⟨e⟩⟩ := setup hV hd hev hn
  refine lowerBound_of_rule e A (fun v s => decide (est v s < 2 * p + 2 + 2)) T
    (fun a b h v => ?_) (fun a b h => ?_)
  · have hed : ((gr a b).comap e).ediam = (2 * p + 2 : ℕ) := by
      rw [comap_ediam]; exact ediam_eq_of_disj a b hp hk h
    have h2 := (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk) v).2
    have h3 : (est v (runOn A e a b T v) : ℕ∞) ≤ ((2 * p + 2 : ℕ) : ℕ∞) + 1 :=
      h2.trans (add_le_add (eccent_le_ediam.trans (le_of_eq hed)) le_rfl)
    have h4 : est v (runOn A e a b T v) ≤ 2 * p + 2 + 1 := by exact_mod_cast h3
    simp only [decide_eq_true_eq]
    omega
  · obtain ⟨u, w, huw⟩ := comap_far e a b hp h
    refine ⟨u, ?_⟩
    have h1 := (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk) u).1
    have h3 : ((2 * p + 4 : ℕ) : ℕ∞) ≤ (est u (runOn A e a b T u) : ℕ∞) :=
      huw.trans (edist_le_eccent.trans h1)
    have h4 : 2 * p + 4 ≤ est u (runOn A e a b T u) := by exact_mod_cast h3
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-- **Lemma 10** of [HW12], `(+,1)`-APSP part: if every node `v` outputs estimates `δ v u` with
`d(v, u) ≤ δ v u ≤ d(v, u) + 1` for all nodes `u` on every connected graph of diameter `d` or
`d + 2`, the bound of Theorem 4 holds. -/
theorem lemma10_apsp_plusOne (hV : Fintype.card V = n) (hd : 4 ≤ d) (hev : Even d) (hn : d + 6 ≤ n)
    (A : Algorithm V (V → Bool) σ B) (δ : V → σ → V → ℕ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (G.diam = d ∨ G.diam = d + 2) → ∀ v u,
        G.dist v u ≤ δ v (A.run G (fun v w => decide (G.Adj v w)) T v) u ∧
          δ v (A.run G (fun v w => decide (G.Adj v w)) T v) u ≤ G.dist v u + 1) :
    (n - 4) / (d + 2) * ((n - 4) / (d + 2)) ≤
      T * (2 * ((2 * ((n - 4) / (d + 2)) + 1) * B)) + 2 := by
  classical
  obtain ⟨p, fa, fb, rfl, hp, hk, ⟨e⟩⟩ := setup hV hd hev hn
  refine lowerBound_of_rule e A (fun v s => decide (∀ u, δ v s u < 2 * p + 2 + 2)) T
    (fun a b h v => ?_) (fun a b h => ?_)
  · have hd' : ((gr a b).comap e).diam = 2 * p + 2 := by
      rw [comap_diam]; exact (lemma9 a b hp hk).1 h
    have hne : ((gr a b).comap e).ediam ≠ ⊤ := by
      rw [comap_ediam]; exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (ediam_le a b hp)
    simp only [decide_eq_true_eq]
    intro u
    have h2 := (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk) v u).2
    have h3 := dist_le_diam hne (u := v) (v := u)
    simp only [runOn]
    omega
  · obtain ⟨u, w, huw⟩ := comap_far e a b hp h
    refine ⟨u, ?_⟩
    have hne : ((gr a b).comap e).edist u w ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENat.natCast_ne_top (2 * p + 4)) ?_
      refine edist_le_ediam.trans ?_
      rw [comap_ediam]; exact ediam_le a b hp
    have h2 : 2 * p + 4 ≤ ((gr a b).comap e).dist u w := by
      have := ENat.toNat_le_toNat huw hne
      rw [ENat.toNat_natCast] at this
      exact this
    have h1 := (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk) u w).1
    simp only [decide_eq_false_iff_not, not_forall, not_lt]
    exact ⟨w, by simp only [runOn]; omega⟩

end Main

/-! ### Randomized version (conditional on the randomized communication complexity of DISJ) -/

section Randomized

/-- The randomized lower bound for set disjointness (Theorem 2 of [HW12], Kalyanasundaram–Schnitger
/ Razborov), as a hypothesis: every private-coin protocol computing `DISJ` on `ι → Bool` with
error `≤ ε` sends at least `κ · |ι|` bits. The coin spaces are nonempty (otherwise the hypothesis
would force `κ ≤ 0`) and `κ` is real (the true constant is `< 1`). Not proved here. -/
def RandDisjLB (ε κ : ℝ) : Prop :=
  ∀ (ι RA RB : Type) [Fintype ι] [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB]
    (P : Protocol ((ι → Bool) × RA) ((ι → Bool) × RB) Bool) (c : ℕ),
    P.RandComputes disj ε → P.CostLE c → κ * Fintype.card ι ≤ c

/-- The number of random strings (one `r v : ρ` per node) on which some node's output is not a
`(+,1)`-approximation of the diameter after `T` rounds. -/
noncomputable def failCount {V σ ρ : Type*} [Fintype V] [Fintype ρ] {B : ℕ}
    (A : Algorithm V ((V → Bool) × ρ) σ B) (est : V → σ → ℕ) (G : SimpleGraph V)
    [DecidableRel G.Adj] (T : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun r : V → ρ => ¬ ∀ v,
    G.diam ≤ est v (A.run G (fun v => (fun w => decide (G.Adj v w), r v)) T v) ∧
      est v (A.run G (fun v => (fun w => decide (G.Adj v w), r v)) T v) ≤ G.diam + 1).card

/-- **Theorem 4** of [HW12], randomized version, conditional on `RandDisjLB ε κ`: a randomized
CONGEST algorithm (private random strings) that, on every connected graph of diameter `d` or
`d + 2`, outputs a `(+,1)`-approximation of the diameter at every node after `T` rounds with
error probability `≤ ε` satisfies `κ k² ≤ T · 2 (2k + 1) B + 2`, `k = ⌊(n - 4)/(d + 2)⌋`. -/
theorem theorem4_randomized {V σ ρ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ]
    {n d B T : ℕ}
    (hV : Fintype.card V = n) (hd : 4 ≤ d) (hev : Even d) (hn : d + 6 ≤ n)
    (A : Algorithm V ((V → Bool) × ρ) σ B) (est : V → σ → ℕ) {ε κ : ℝ} (hCC : RandDisjLB ε κ)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
      (G.diam = d ∨ G.diam = d + 2) → (failCount A est G T : ℝ) ≤ ε * Fintype.card (V → ρ)) :
    κ * ((n - 4) / (d + 2) * ((n - 4) / (d + 2)) : ℕ) ≤
      ((T * (2 * ((2 * ((n - 4) / (d + 2)) + 1) * B)) + 2 : ℕ) : ℝ) := by
  classical
  obtain ⟨p, fa, fb, rfl, hp, hk, ⟨e⟩⟩ := setup hV hd hev hn
  set k := (n - 4) / (2 * p + 2 + 2)
  let o : V → σ → Bool := fun v s => decide (est v s < 2 * p + 2 + 2)
  have hle : ∀ a b, LBFamily.Algorithm.randErr (withOut A o) ((fam e).G a b) ((fam e).inp a b) T
      (disj a b) ≤ failCount A est ((gr a b).comap e) T := by
    intro a b
    unfold LBFamily.Algorithm.randErr failCount
    refine Finset.card_le_card fun r => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hr hgood
    apply hr
    simp only [Algorithm.Accepts, withOut_run]
    change decide (∀ v, o v (A.run ((gr a b).comap e)
      (fun v => (fun w => decide (((gr a b).comap e).Adj v w), r v)) T v) = true) = disj a b
    cases h : disj a b
    · have hdiam : ((gr a b).comap e).diam = 2 * p + 4 := by
        rw [comap_diam]; exact (lemma8 a b hp h).2
      have := (hgood (e.symm c0)).1
      simp only [decide_eq_false_iff_not, not_forall]
      exact ⟨e.symm c0, by simp only [o, decide_eq_true_eq]; omega⟩
    · have hdiam : ((gr a b).comap e).diam = 2 * p + 2 := by
        rw [comap_diam]; exact (lemma9 a b hp hk).1 h
      simp only [decide_eq_true_eq]
      intro v
      have := (hgood v).2
      simp only [o, decide_eq_true_eq]
      omega
  have h := (fam e).rand_lowerBound (withOut A o) T disj ε (fun a b => le_trans
    ((Nat.cast_le (α := ℝ)).2 (hle a b))
    (hA _ (comap_connected e a b hp) (comap_diam_mem e a b hp hk)))
    (Nat.ceil (κ * ((k * k : ℕ) : ℝ))) (fun P c hP hc => Nat.ceil_le.2 (by
      have := hCC _ _ _ P c hP hc
      simpa using this))
  have hcut := fam_card e
  calc κ * ((k * k : ℕ) : ℝ) ≤ ((Nat.ceil (κ * ((k * k : ℕ) : ℝ))) : ℝ) := Nat.le_ceil _
    _ ≤ (((fam e).Ecut.card * B * 2 * T + 2 : ℕ) : ℝ) := by
        exact_mod_cast h.trans (le_of_eq (by ring))
    _ ≤ _ := by
        have : (fam e).Ecut.card * B * 2 * T ≤ T * (2 * ((2 * k + 1) * B)) := by
          calc (fam e).Ecut.card * B * 2 * T ≤ (2 * k + 1) * B * 2 * T := by gcongr
            _ = _ := by ring
        exact_mod_cast (by omega : (fam e).Ecut.card * B * 2 * T + 2 ≤
          T * (2 * ((2 * k + 1) * B)) + 2)

end Randomized

/-! ### Non-vacuity -/

section NonVacuity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph a node reconstructs from a (partial) table of adjacency rows. -/
def recon (s : V → Option (V → Bool)) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => (s x).getD (fun _ => false) y = true

lemma recon_run_eq (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ} (hD : G.ediam ≤ D) (v : V) :
    recon ((gatherInputsAlg V (V → Bool)).run G (fun v w => decide (G.Adj v w)) D v) = G := by
  rw [gatherInputs_run_of_ediam G _ hD v]
  exact fromRel_adjInput G

omit [DecidableEq V] in
lemma ediam_le_of_diam {G : SimpleGraph V} {D : ℕ} (hG : G.Connected) (h : G.diam ≤ D) :
    G.ediam ≤ D := by
  have : Nonempty V := hG.nonempty
  have hne : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.1 hG
  rw [← ENat.natCast_toNat hne]
  exact_mod_cast h

/-- Non-vacuity of the hypothesis of Theorem 4: full-information flooding for `d + 2` rounds
(messages of `gatherInputsBits V (V → Bool)` bits) followed by a local computation outputs the
exact diameter on every connected graph of diameter `d` or `d + 2`. -/
theorem theorem4_hyp_satisfiable (d : ℕ) :
    ∃ (B : ℕ) (A : Algorithm V (V → Bool) (V → Option (V → Bool)) B)
      (est : V → (V → Option (V → Bool)) → ℕ),
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        (G.diam = d ∨ G.diam = d + 2) → ∀ v,
          G.diam ≤ est v (A.run G (fun v w => decide (G.Adj v w)) (d + 2) v) ∧
            est v (A.run G (fun v w => decide (G.Adj v w)) (d + 2) v) ≤ G.diam + 1 := by
  refine ⟨_, gatherInputsAlg V (V → Bool), fun _ s => (recon s).diam, fun G _ hG hd v => ?_⟩
  beta_reduce
  rw [recon_run_eq G (ediam_le_of_diam hG (by omega)) v]
  omega

/-- Non-vacuity of the hypothesis of Lemma 10 (APSP part): flooding for `d + 2` rounds yields
exact distances. -/
theorem lemma10_apsp_plusOne_hyp_satisfiable (d : ℕ) :
    ∃ (B : ℕ) (A : Algorithm V (V → Bool) (V → Option (V → Bool)) B)
      (δ : V → (V → Option (V → Bool)) → V → ℕ),
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        (G.diam = d ∨ G.diam = d + 2) → ∀ v u,
          G.dist v u ≤ δ v (A.run G (fun v w => decide (G.Adj v w)) (d + 2) v) u ∧
            δ v (A.run G (fun v w => decide (G.Adj v w)) (d + 2) v) u ≤ G.dist v u + 1 := by
  refine ⟨_, gatherInputsAlg V (V → Bool), fun v s u => (recon s).dist v u,
    fun G _ hG hd v u => ?_⟩
  beta_reduce
  rw [recon_run_eq G (ediam_le_of_diam hG (by omega)) v]
  omega

end NonVacuity

end Podc.OptimalAPSP
