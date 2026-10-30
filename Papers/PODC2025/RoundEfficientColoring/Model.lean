import Podc.Foundations.Combinatorics.SimpleGraph.EdgeColoring.Basic
import Podc.Computability.CommunicationComplexity.OneRound

/-!
# The two-party edge colouring problem

Chang–Mishra–Nguyen–Salim, *Round and Communication Efficient Graph Coloring*, PODC 2025,
Section 3.1. The vertex set `V` (and `n = |V|`, `Δ`) are known to both parties; the edges of the
input graph `G = A ⊔ B` are partitioned between Alice (`A`) and Bob (`B`), and `G` has maximum
degree `≤ Δ`. In the edge colouring problem each party outputs colours for **its own edges** only;
the outputs solve the `k`-edge colouring problem if together they form a proper edge colouring of
`G` with the colours `0, …, k - 1`.

Colourings are functions `Sym2 V → ℕ` (`SimpleGraph.IsProperEdgeColoring`). Degrees are
`(G.neighborSet v).ncard`.

This file also contains the deferral procedure shared by Theorem 3 and Algorithm 2: repeatedly
move an edge both of whose endpoints have (current) degree `≥ θ` from the remaining graph to the
deferred graph (`exists_deferral`).
-/

namespace Podc.RoundEfficientColoring

open SimpleGraph

variable {V : Type*}

open Classical in
/-- The combined colouring: Alice's colours on her edges, Bob's colours on the other edges. -/
noncomputable def combine (A : SimpleGraph V) (cA cB : Sym2 V → ℕ) : Sym2 V → ℕ :=
  fun e => if e ∈ A.edgeSet then cA e else cB e

/-- A valid input with maximum degree `≤ Δ`: Alice's and Bob's edge sets are disjoint and the
graph `A ⊔ B` has maximum degree at most `Δ`. -/
def ValidInput (Δ : ℕ) (A B : SimpleGraph V) : Prop :=
  Disjoint A B ∧ ∀ v, ((A ⊔ B).neighborSet v).ncard ≤ Δ

/-- Alice's colouring `cA` (of her edges) and Bob's colouring `cB` (of his edges) solve the
`k`-edge colouring problem on the input `(A, B)`. -/
def SolvesEdgeColoring (k : ℕ) (A B : SimpleGraph V) (cA cB : Sym2 V → ℕ) : Prop :=
  (A ⊔ B).IsProperEdgeColoring (combine A cA cB) k

lemma combine_of_left {A : SimpleGraph V} {cA cB : Sym2 V → ℕ} {u v : V} (h : A.Adj u v) :
    combine A cA cB s(u, v) = cA s(u, v) := by
  simp [combine, h]

lemma combine_of_right {A B : SimpleGraph V} (hAB : Disjoint A B) {cA cB : Sym2 V → ℕ} {u v : V}
    (h : B.Adj u v) : combine A cA cB s(u, v) = cB s(u, v) := by
  have : ¬ A.Adj u v := fun h' => by
    have := hAB.le_bot ⟨h', h⟩
    exact this
  simp [combine, this]

/-- Degrees add up over a partition of the edges. -/
lemma ncard_neighborSet_sup [Finite V] {A B : SimpleGraph V} (hAB : Disjoint A B) (v : V) :
    ((A ⊔ B).neighborSet v).ncard = (A.neighborSet v).ncard + (B.neighborSet v).ncard := by
  rw [neighborSet_sup]
  refine Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)
  rw [Set.disjoint_left]
  intro w hA hB
  exact hAB.le_bot ⟨hA, hB⟩

/-- To check a solution it suffices to check both parties' colourings and the pairs consisting of
an edge of Alice and an edge of Bob at a common vertex. -/
lemma solvesEdgeColoring_of {k : ℕ} {A B : SimpleGraph V} (hAB : Disjoint A B)
    {cA cB : Sym2 V → ℕ} (hA : A.IsProperEdgeColoring cA k) (hB : B.IsProperEdgeColoring cB k)
    (hcross : ∀ ⦃v w w' : V⦄, A.Adj v w → B.Adj v w' → cA s(v, w) ≠ cB s(v, w')) :
    SolvesEdgeColoring k A B cA cB := by
  refine ⟨fun u v huv => ?_, fun u v w huv huw he => ?_⟩
  · rcases huv with h | h
    · rw [combine_of_left h]; exact hA.1 h
    · rw [combine_of_right hAB h]; exact hB.1 h
  · rcases huv with h1 | h1 <;> rcases huw with h2 | h2
    · rw [combine_of_left h1, combine_of_left h2] at he; exact hA.2 h1 h2 he
    · rw [combine_of_left h1, combine_of_right hAB h2] at he; exact absurd he (hcross h1 h2)
    · rw [combine_of_right hAB h1, combine_of_left h2] at he; exact absurd he.symm (hcross h2 h1)
    · rw [combine_of_right hAB h1, combine_of_right hAB h2] at he; exact hB.2 h1 h2 he

/-! ### Deferral -/

lemma neighborSet_sdiff_of_le {X R : SimpleGraph V} (v : V) :
    (X \ R).neighborSet v = X.neighborSet v \ R.neighborSet v := by
  ext w; simp

lemma ncard_neighborSet_sdiff [Finite V] {X R : SimpleGraph V} (hRX : R ≤ X) (v : V) :
    ((X \ R).neighborSet v).ncard = (X.neighborSet v).ncard - (R.neighborSet v).ncard := by
  rw [neighborSet_sdiff_of_le]
  exact Set.ncard_sdiff (fun w hw => hRX hw) (Set.toFinite _)

lemma ncard_neighborSet_le_of_le [Finite V] {X R : SimpleGraph V} (hRX : R ≤ X) (v : V) :
    (R.neighborSet v).ncard ≤ (X.neighborSet v).ncard :=
  Set.ncard_le_ncard (fun _ hw => hRX hw) (Set.toFinite _)

/-- **The deferral procedure** (Theorem 3 with `θ = Δ`, Algorithm 2 lines 1–5 with `θ = Δ - 1`):
starting from `R = X`, repeatedly remove from `R` an edge both of whose endpoints have
`R`-degree `≥ θ`. The result `R ≤ X` has no edge between two vertices of `R`-degree `≥ θ`, and
every vertex that lost an edge still has `R`-degree `≥ θ - 1` (it had `R`-degree `≥ θ` before
its last loss). -/
theorem exists_deferral [Finite V] (X : SimpleGraph V) (θ : ℕ) :
    ∃ R ≤ X, (∀ ⦃u v : V⦄, R.Adj u v → (R.neighborSet u).ncard < θ ∨ (R.neighborSet v).ncard < θ)
      ∧ ∀ v, (R.neighborSet v).ncard < (X.neighborSet v).ncard → θ ≤ (R.neighborSet v).ncard + 1 := by
  suffices h : ∀ n, ∀ R ≤ X, R.edgeSet.ncard = n →
      (∀ v, (R.neighborSet v).ncard < (X.neighborSet v).ncard → θ ≤ (R.neighborSet v).ncard + 1) →
      ∃ R' ≤ X, (∀ ⦃u v : V⦄, R'.Adj u v →
        (R'.neighborSet u).ncard < θ ∨ (R'.neighborSet v).ncard < θ)
      ∧ ∀ v, (R'.neighborSet v).ncard < (X.neighborSet v).ncard →
        θ ≤ (R'.neighborSet v).ncard + 1 from
    h _ X le_rfl rfl (fun v hv => absurd hv (lt_irrefl _))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hRX hn hinv
  by_cases hterm : ∀ ⦃u v : V⦄, R.Adj u v →
      (R.neighborSet u).ncard < θ ∨ (R.neighborSet v).ncard < θ
  · exact ⟨R, hRX, hterm, hinv⟩
  push Not at hterm
  obtain ⟨u, v, huv, hu, hv⟩ := hterm
  refine ih _ (hn ▸ ncard_edgeSet_deleteEdges_lt (G := R) huv) (R.deleteEdges {s(u, v)})
    ((deleteEdges_le _).trans hRX) rfl fun w hw => ?_
  by_cases hwu : w = u
  · subst hwu
    have := ncard_neighborSet_deleteEdges_self huv
    omega
  by_cases hwv : w = v
  · subst hwv
    have := ncard_neighborSet_deleteEdges_self huv.symm
    rw [Sym2.eq_swap] at this
    omega
  have heq : (R.deleteEdges {s(u, v)}).neighborSet w = R.neighborSet w := by
    ext x
    simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff, and_iff_left_iff_imp]
    intro _ he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hwu rfl
    · exact hwv rfl
  rw [heq] at hw ⊢
  exact hinv w hw

end Podc.RoundEfficientColoring
