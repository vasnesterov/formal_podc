import Papers.PODC2019.LocalBroadcastBC.Necessity
import Papers.PODC2019.LocalBroadcastBC.Sufficiency
import Papers.PODC2019.LocalBroadcastBC.Counterexample

/-!
# Main result of [KNV19]: the tight condition for exact Byzantine consensus under local broadcast

M. S. Khan, S. S. Naqvi, N. H. Vaidya. *Exact Byzantine Consensus on Undirected Graphs under
Local Broadcast Model.* PODC 2019 (arXiv:1903.11677).

* `consensus_iff`: for `f < n` and `n ≥ 2`, binary Byzantine consensus tolerating `f` faults is
  solvable under local broadcast on `G` iff `G` has minimum degree `≥ 2f` and is
  `(⌊3f/2⌋ + 1)`-connected (Theorems 4.1 and 5.1).
* `complete_iff`: on the complete graph the condition is `n ≥ 2f + 1` (remark in Section 2).
-/

open Cslib.Byzantine.LockStep

namespace LocalBroadcastBC

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Theorems 4.1 and 5.1** of [KNV19]: for `f < n` and `n ≥ 2`, Byzantine consensus tolerating
at most `f` Byzantine faults is solvable under the local broadcast model on `G` iff `G` has
minimum degree at least `2f` and is `(⌊3f/2⌋ + 1)`-connected. -/
theorem consensus_iff {f : ℕ} (hfn : f < Fintype.card V) (hn : 2 ≤ Fintype.card V) :
    SolvableLB G (atMost f) (Consensus : Spec V Bool Bool) ↔
      2 * f ≤ G.minDegree ∧ G.IsVertexConnected (3 * f / 2 + 1) :=
  ⟨fun h => theorem_4_1 h hfn hn, fun h => theorem_5_1 h.1 h.2⟩

/-- The complete graph on `n` vertices is `(n - 1)`-connected (in the sense of `k`-connectivity
for every `k < n`). -/
lemma top_isVertexConnected {k : ℕ} (hk : k < Fintype.card V) :
    (⊤ : SimpleGraph V).IsVertexConnected k := by
  refine ⟨hk, fun X _ u v hu hv => ?_⟩
  by_cases huv : u = v
  · subst huv; exact ⟨SimpleGraph.Walk.nil, by simpa using hu⟩
  · refine ⟨SimpleGraph.Walk.cons (show (⊤ : SimpleGraph V).Adj u v from huv) .nil, ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption_mod_cast

/-- On the complete graph (local broadcast = global broadcast), the condition of [KNV19] is
`n ≥ 2f + 1`, as for Rabin–Ben-Or's global broadcast model (remark in Section 2). -/
theorem complete_iff {f : ℕ} (hfn : f < Fintype.card V) (hn : 2 ≤ Fintype.card V) :
    SolvableLB (⊤ : SimpleGraph V) (atMost f) (Consensus : Spec V Bool Bool) ↔
      2 * f + 1 ≤ Fintype.card V := by
  rw [consensus_iff hfn hn]
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hmin : (⊤ : SimpleGraph V).minDegree = Fintype.card V - 1 := by
    obtain ⟨v⟩ := id hne
    apply le_antisymm
    · exact ((⊤ : SimpleGraph V).minDegree_le_degree v).trans (by simp)
    · exact SimpleGraph.le_minDegree_of_forall_le_degree _ _ fun w => by simp
  rw [hmin]
  constructor
  · rintro ⟨h, -⟩; omega
  · intro h
    refine ⟨by omega, top_isVertexConnected ?_⟩
    rcases Nat.eq_zero_or_pos f with rfl | hf <;> omega

end LocalBroadcastBC
