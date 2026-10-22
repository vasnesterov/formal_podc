import Papers.PODC2012.ResilientRouting.Model

/-!
# The network of Figure 3

The 12-node network of Figure 3 of the paper: the destination `d = 0`, a centre `1` adjacent to
`2, 3, 4, 5`, and for each of the six pairs of `{2, 3, 4, 5}` a node adjacent to both members of
the pair and to `d`:

| node | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|
| pair | 2,3 | 3,4 | 4,5 | 5,2 | 2,4 | 3,5 |

(read off the figure: `2–6–3`, `3–7–4`, `4–8–5`, `5–9–2`, `2–10–4`, `3–11–5`, all of `6,…,11`
adjacent to `d`; 22 edges).

Failure scenarios are given by the list of *surviving* edges; computations on them are by
`decide`.
-/

namespace Podc.ResilientRouting.Fig3

open SimpleGraph

/-- The edges of Figure 3. -/
def edges : List (Fin 12 × Fin 12) :=
  [(1, 2), (1, 3), (1, 4), (1, 5),
   (2, 6), (6, 3), (6, 0), (3, 7), (7, 4), (7, 0), (4, 8), (8, 5), (8, 0), (5, 9), (9, 2), (9, 0),
   (2, 10), (10, 4), (10, 0), (3, 11), (11, 5), (11, 0)]

/-- Membership of an unordered pair in a list of pairs. -/
def memB (L : List (Fin 12 × Fin 12)) (u v : Fin 12) : Bool :=
  L.any fun p => (p.1 = u ∧ p.2 = v) || (p.1 = v ∧ p.2 = u)

theorem memB_comm (L : List (Fin 12 × Fin 12)) (u v : Fin 12) : memB L u v = memB L v u := by
  unfold memB
  congr 1
  funext p
  rw [Bool.or_comm]

/-- The network of Figure 3. -/
def G : SimpleGraph (Fin 12) where
  Adj u v := memB edges u v = true
  symm := ⟨fun u v h => by rwa [memB_comm]⟩
  loopless := ⟨fun u h => by revert u h; decide⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (memB edges u v = true))

/-- The destination. -/
abbrev d : Fin 12 := 0

/-- The failure scenario in which exactly the edges of `L` survive. -/
def scen (L : List (Fin 12 × Fin 12)) : Set (Sym2 (Fin 12)) :=
  {e | e ∈ G.edgeSet ∧ ¬ Sym2.lift ⟨fun u v => memB L u v = true, fun u v => by simp only [memB_comm]⟩ e}

theorem scen_subset (L : List (Fin 12 × Fin 12)) : scen L ⊆ G.edgeSet := fun _ h => h.1

theorem live_scen {L : List (Fin 12 × Fin 12)} {u v : Fin 12} :
    Live G (scen L) u v ↔ G.Adj u v ∧ memB L u v = true := by
  simp only [Live, scen, Set.mem_ofPred_eq, mem_edgeSet, Sym2.lift_mk, not_and, not_not]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

instance (L : List (Fin 12 × Fin 12)) (u v : Fin 12) : Decidable (Live G (scen L) u v) :=
  decidable_of_iff _ live_scen.symm

theorem reachable_of_live {L : List (Fin 12 × Fin 12)} {u v : Fin 12}
    (h : Live G (scen L) u v) : (G.deleteEdges (scen L)).Reachable u v :=
  (deleteEdges_adj.2 h).reachable

/-- The neighbours of node `1`: its view when its four links are up. -/
def A1 : Set (Fin 12) := {u | G.Adj 1 u}

theorem view_eq_A1 {L : List (Fin 12 × Fin 12)}
    (h : ∀ u, G.Adj 1 u → memB L 1 u = true) : view G (scen L) 1 = A1 := by
  ext u
  simp only [view, A1, Set.mem_ofPred_eq, live_scen]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h u h'⟩⟩

theorem view_congr {L L' : List (Fin 12 × Fin 12)} {v : Fin 12}
    (h : ∀ u, memB L v u = memB L' v u) : view G (scen L) v = view G (scen L') v := by
  ext u
  simp only [view, Set.mem_ofPred_eq, live_scen, h u]

/-- The node adjacent to `d` and to both nodes of a pair of `{2,3,4,5}`. -/
def mid (a b : Fin 12) : Fin 12 :=
  if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 6
  else if (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) then 7
  else if (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) then 8
  else if (a = 5 ∧ b = 2) ∨ (a = 2 ∧ b = 5) then 9
  else if (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) then 10
  else 11

theorem connected : G.Connected := by
  have h : ∀ v, G.Reachable v 0 := by
    have r : ∀ u v, G.Adj u v → G.Reachable u v := fun _ _ h => h.reachable
    have r6 : G.Reachable 6 0 := r _ _ (by decide)
    have r2 : G.Reachable 2 0 := (r 2 6 (by decide)).trans r6
    have r3 : G.Reachable 3 0 := (r 3 6 (by decide)).trans r6
    have r4 : G.Reachable 4 0 := (r 4 7 (by decide)).trans (r _ _ (by decide))
    have r5 : G.Reachable 5 0 := (r 5 8 (by decide)).trans (r _ _ (by decide))
    intro v
    fin_cases v
    · rfl
    · exact (r 1 2 (by decide)).trans r2
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6
    all_goals exact r _ _ (by decide)
  exact (connected_iff_exists_forall_reachable G).2 ⟨0, fun v => (h v).symm⟩

end Podc.ResilientRouting.Fig3
