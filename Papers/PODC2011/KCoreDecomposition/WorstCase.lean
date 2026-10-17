import Papers.PODC2011.KCoreDecomposition.Trajectory

/-!
# Worst-case examples for the synchronous execution time (§4.2)

* `worstGraph N` — the family of Fig. 3 (the paper's "worst case"). We prove its degrees
  (`worstGraph_degree`), that every node has coreness `2` (`coreness_worstGraph`) and the explicit
  synchronous trajectory (`traj_worstGraph`), hence `stab_worstGraph : stab (worstGraph N) = N - 3`
  for `N ≥ 5`.
* `stab_pathGraph : stab (pathGraph N) = (N - 1) / 2` — the "linear chain" remark.
* `fig2Graph` — the six-node example of Fig. 2: corenesses `(1,2,2,2,2,1)` and `stab = 2`.

Recall that `stab G` is the number of synchronous update steps after which all estimates are
correct.
-/

open Finset

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

/-! ### Generic bounds on the h-index -/

section Generic

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If all neighbours have estimate `≥ i` and the degree is `≥ i`, the h-index is `≥ i`. -/
theorem le_hIndex_of_forall_adj {e : V → ℕ∞} {u : V} {i : ℕ}
    (h : ∀ v, G.Adj u v → (i : ℕ∞) ≤ e v) (hi : i ≤ G.degree u) : i ≤ hIndex G e u := by
  rw [le_hIndex_iff, nbrCount,
    filter_true_of_mem fun v hv => h v ((G.mem_neighborFinset u v).1 hv),
    G.card_neighborFinset_eq_degree]
  exact hi

/-- If `i` given neighbours have estimate `≥ i`, the h-index is `≥ i`. -/
theorem le_hIndex_of_subset {e : V → ℕ∞} {u : V} {i : ℕ} (W : Finset V)
    (hW : ∀ v ∈ W, G.Adj u v ∧ (i : ℕ∞) ≤ e v) (hi : i ≤ #W) : i ≤ hIndex G e u := by
  rw [le_hIndex_iff]
  refine hi.trans (card_le_card fun v hv => ?_)
  rw [mem_filter, SimpleGraph.mem_neighborFinset]
  exact hW v hv

/-- If all neighbours with estimate `≥ i` lie in a set of size `< i`, the h-index is `< i`. -/
theorem hIndex_lt_of_subset {e : V → ℕ∞} {u : V} {i : ℕ} (W : Finset V)
    (hW : ∀ v, G.Adj u v → (i : ℕ∞) ≤ e v → v ∈ W) (hi : #W < i) : hIndex G e u < i := by
  refine lt_of_not_ge fun hle => ?_
  have h1 := le_hIndex_iff.1 hle
  have h2 : nbrCount G e u i ≤ #W := card_le_card fun v hv => by
    rw [mem_filter, SimpleGraph.mem_neighborFinset] at hv
    exact hW v hv.1 hv.2
  omega

/-- If a node of degree `≤ i` has a neighbour with estimate `< i`, its h-index is `< i`. -/
theorem hIndex_lt_of_adj {e : V → ℕ∞} {u v : V} {i : ℕ} (huv : G.Adj u v) (hv : e v < i)
    (hd : G.degree u ≤ i) : hIndex G e u < i := by
  refine hIndex_lt_of_subset ((G.neighborFinset u).erase v) (fun w hw hiw => ?_) ?_
  · refine mem_erase.2 ⟨?_, (G.mem_neighborFinset u w).2 hw⟩
    rintro rfl; exact (not_le.2 hv) hiw
  · rw [card_erase_of_mem ((G.mem_neighborFinset u v).2 huv), G.card_neighborFinset_eq_degree]
    have : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨v, huv⟩
    omega

/-- When the cap and the h-index are both `≥ 1`, `computeIndex` is their minimum. -/
theorem computeIndex_eq_min' {e : V → ℕ∞} {u : V} {k : ℕ} (hk : 1 ≤ k)
    (hh : 1 ≤ hIndex G e u) : computeIndex G e u k = min k (hIndex G e u) := by
  rw [computeIndex_eq]; split_ifs <;> omega

end Generic

/-- Cardinality helpers for finsets of `Fin N` described by the values of their elements. -/
theorem card_eq_two_of_val {N : ℕ} (s : Finset (Fin N)) (x y : ℕ) (hx : x < N) (hy : y < N)
    (hxy : x ≠ y) (hs : ∀ v : Fin N, v ∈ s ↔ v.val = x ∨ v.val = y) : #s = 2 := by
  rw [card_eq_two]
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, by simp [Fin.ext_iff, hxy], ?_⟩
  ext v; rw [hs]; simp [Fin.ext_iff]

theorem card_eq_three_of_val {N : ℕ} (s : Finset (Fin N)) (x y z : ℕ) (hx : x < N) (hy : y < N)
    (hz : z < N) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : ∀ v : Fin N, v ∈ s ↔ v.val = x ∨ v.val = y ∨ v.val = z) : #s = 3 := by
  rw [card_eq_three]
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, by simp [Fin.ext_iff, hxy], by simp [Fin.ext_iff, hxz],
    by simp [Fin.ext_iff, hyz], ?_⟩
  ext v; rw [hs]; simp [Fin.ext_iff]

/-! ### The worst-case family of Fig. 3 -/

/-- Edge relation of the graph of Fig. 3 on 0-based labels (`a` is the paper's node `a + 1`):
the path `0 — 1 — ⋯ — N−2`, the hub `N−1` joined to every node except `N−4`, and the extra edge
`N−4 — N−2`. -/
def worstE (N a b : ℕ) : Prop :=
  (b = a + 1 ∧ b ≤ N - 2) ∨ (b = N - 1 ∧ a ≠ N - 4) ∨ (a = N - 4 ∧ b = N - 2)

instance (N a b : ℕ) : Decidable (worstE N a b) := by unfold worstE; infer_instance

/-- The "worst-case" graph of Fig. 3. Vertex `i : Fin N` is the paper's node `i + 1`:
node `N` (the hub) is connected to all nodes except `N − 3`; node `i` is connected to `i + 1` for
`i = 1, …, N − 2`; node `N − 3` is also connected to `N − 1`. -/
def worstGraph (N : ℕ) : SimpleGraph (Fin N) where
  Adj i j := i.val ≠ j.val ∧ (worstE N i.val j.val ∨ worstE N j.val i.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (N : ℕ) : DecidableRel (worstGraph N).Adj := fun i j =>
  inferInstanceAs (Decidable (i.val ≠ j.val ∧ (worstE N i.val j.val ∨ worstE N j.val i.val)))

theorem worstGraph_adj {N : ℕ} {i j : Fin N} :
    (worstGraph N).Adj i j ↔
      i.val ≠ j.val ∧ (worstE N i.val j.val ∨ worstE N j.val i.val) := Iff.rfl

/-- Degrees in the graph of Fig. 3 (as stated in the paper): the hub has degree `N − 2`, node `1`
has degree `2`, all other nodes have degree `3`. -/
theorem worstGraph_degree {N : ℕ} (hN : 5 ≤ N) (u : Fin N) :
    (worstGraph N).degree u = if u.val = N - 1 then N - 2 else if u.val = 0 then 2 else 3 := by
  have hu := u.isLt
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have mem : ∀ v : Fin N, v ∈ (worstGraph N).neighborFinset u ↔
      u.val ≠ v.val ∧ (worstE N u.val v.val ∨ worstE N v.val u.val) := fun v => by
    rw [SimpleGraph.mem_neighborFinset, worstGraph_adj]
  split_ifs with h1 h0
  · have : (worstGraph N).neighborFinset u = (univ.erase u).erase ⟨N - 4, by omega⟩ := by
      ext v
      simp only [mem_erase, mem_univ, and_true, ne_eq, Fin.ext_iff]
      rw [mem]; unfold worstE
      have := v.isLt
      omega
    rw [this, card_erase_of_mem
        (by simp only [mem_erase, mem_univ, and_true, ne_eq, Fin.ext_iff]; omega),
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega
  · refine card_eq_two_of_val _ 1 (N - 1) (by omega) (by omega) (by omega) fun v => ?_
    rw [mem]; unfold worstE; have := v.isLt; omega
  · rcases (by omega : u.val ≤ N - 5 ∨ u.val = N - 4 ∨ u.val = N - 3 ∨ u.val = N - 2) with
      h | h | h | h
    · refine card_eq_three_of_val _ (u.val - 1) (u.val + 1) (N - 1) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) fun v => ?_
      rw [mem]; unfold worstE; have := v.isLt; omega
    · refine card_eq_three_of_val _ (N - 5) (N - 3) (N - 2) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) fun v => ?_
      rw [mem]; unfold worstE; have := v.isLt; omega
    · refine card_eq_three_of_val _ (N - 4) (N - 2) (N - 1) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) fun v => ?_
      rw [mem]; unfold worstE; have := v.isLt; omega
    · refine card_eq_three_of_val _ (N - 4) (N - 3) (N - 1) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) fun v => ?_
      rw [mem]; unfold worstE; have := v.isLt; omega

/-- The explicit synchronous trajectory on the graph of Fig. 3 (0-based labels): node `0` stays at
`2`; the hub `N−1` has `N−2` at step `0`, `3` for `1 ≤ s < N−4` and `2` afterwards; any other node
`a` has `3` for `s < min a (N−3)` and `2` afterwards. -/
def worstTraj (N s a : ℕ) : ℕ :=
  if a = N - 1 then (if s = 0 then N - 2 else if s < N - 4 then 3 else 2)
  else if s < min a (N - 3) then 3 else 2

theorem two_le_worstTraj {N : ℕ} (hN : 5 ≤ N) (s a : ℕ) : 2 ≤ worstTraj N s a := by
  unfold worstTraj; split_ifs <;> omega

theorem worstTraj_le_three {N : ℕ} (s a : ℕ) (ha : a ≠ N - 1) : worstTraj N s a ≤ 3 := by
  unfold worstTraj; split_ifs <;> omega

/-- The synchronous trajectory on the graph of Fig. 3 is `worstTraj`. -/
theorem traj_worstGraph {N : ℕ} (hN : 5 ≤ N) (s : ℕ) (u : Fin N) :
    traj (worstGraph N) s u = worstTraj N s u.val := by
  induction s generalizing u with
  | zero =>
    rw [traj_zero, worstGraph_degree hN]
    unfold worstTraj; split_ifs <;> omega
  | succ s ih =>
    have hfun : traj (worstGraph N) s = fun v => worstTraj N s v.val := funext ih
    have hu := u.isLt
    have hdeg := worstGraph_degree hN u
    have cast_le : ∀ (i : ℕ) (v : Fin N), ((i : ℕ∞) ≤ toE (fun w : Fin N => worstTraj N s w.val) v
        ↔ i ≤ worstTraj N s v.val) := fun i v => Nat.cast_le
    have cast_lt : ∀ (i : ℕ) (v : Fin N), (toE (fun w : Fin N => worstTraj N s w.val) v < (i : ℕ∞)
        ↔ worstTraj N s v.val < i) := fun i v => Nat.cast_lt
    have h2 : 2 ≤ hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u :=
      le_hIndex_of_forall_adj (fun v _ => (cast_le 2 v).2 (two_le_worstTraj hN s _))
        (by rw [hdeg]; split_ifs <;> omega)
    have hk : 1 ≤ worstTraj N s u.val := by have := two_le_worstTraj hN s u.val; omega
    rw [traj_succ_apply, hfun]
    beta_reduce
    rw [computeIndex_eq_min' hk (le_trans (by norm_num : 1 ≤ 2) h2)]
    by_cases hhub : u.val = N - 1
    · -- the hub
      have h3 : hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u < 4 :=
        hIndex_lt_of_subset ∅ (fun v huv hv => by
          rw [cast_le] at hv
          have := worstTraj_le_three (N := N) s v.val (by rw [worstGraph_adj] at huv; omega)
          omega) (by simp)
      by_cases hs : s + 1 < N - 4
      · have h3' : 3 ≤ hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u := by
          refine le_hIndex_of_subset {⟨N - 5, by omega⟩, ⟨N - 3, by omega⟩, ⟨N - 2, by omega⟩}
            (fun v hv => ?_) ?_
          · simp only [mem_insert, mem_singleton, Fin.ext_iff] at hv
            rw [worstGraph_adj, cast_le]
            refine ⟨by unfold worstE; omega, ?_⟩
            unfold worstTraj; split_ifs <;> omega
          · rw [card_eq_three_of_val _ (N - 5) (N - 3) (N - 2) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (fun v => by simp [Fin.ext_iff])]
        generalize hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u = H at *
        unfold worstTraj; split_ifs <;> first | omega | contradiction
      · have h2' : hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u < 3 := by
          refine hIndex_lt_of_subset {⟨N - 3, by omega⟩, ⟨N - 2, by omega⟩}
            (fun v huv hv => ?_) (card_le_two.trans_lt (by norm_num))
          rw [worstGraph_adj] at huv
          rw [cast_le] at hv
          simp only [mem_insert, mem_singleton, Fin.ext_iff]
          unfold worstE at huv
          have := v.isLt
          unfold worstTraj at hv; split_ifs at hv <;> omega
        generalize hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u = H at *
        unfold worstTraj; split_ifs <;> first | omega | contradiction
    · -- a non-hub node
      have hle3 := (hIndex_le_degree (G := worstGraph N)
        (toE fun v => worstTraj N s v.val) u).trans_eq hdeg
      by_cases hs : s + 1 < min u.val (N - 3)
      · have h3 : 3 ≤ hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u := by
          refine le_hIndex_of_forall_adj (fun v huv => ?_) (by rw [hdeg]; split_ifs <;> omega)
          rw [cast_le]
          rw [worstGraph_adj] at huv
          unfold worstE at huv
          have := v.isLt
          unfold worstTraj; split_ifs <;> omega
        generalize hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u = H at *
        unfold worstTraj; split_ifs at hle3 ⊢ <;> omega
      · by_cases hcur : s < min u.val (N - 3)
        · -- a neighbour already has the value `2`
          have hlt : hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u < 3 := by
            by_cases ha : u.val ≤ N - 4
            · refine hIndex_lt_of_adj (v := ⟨u.val - 1, by omega⟩) ?_ ?_
                (by rw [hdeg]; split_ifs <;> omega)
              · rw [worstGraph_adj]; dsimp only; unfold worstE; omega
              · rw [cast_lt]; dsimp only; unfold worstTraj; split_ifs <;> omega
            · refine hIndex_lt_of_adj (v := ⟨N - 4, by omega⟩) ?_ ?_
                (by rw [hdeg]; split_ifs <;> omega)
              · rw [worstGraph_adj]; dsimp only; unfold worstE; omega
              · rw [cast_lt]; dsimp only; unfold worstTraj; split_ifs <;> omega
          generalize hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u = H at *
          unfold worstTraj; split_ifs; omega
        · generalize hIndex (worstGraph N) (toE fun v => worstTraj N s v.val) u = H at *
          unfold worstTraj; split_ifs; omega

/-- Every node of the graph of Fig. 3 has coreness `2`. -/
theorem coreness_worstGraph {N : ℕ} (hN : 5 ≤ N) (u : Fin N) :
    coreness (worstGraph N) u = 2 := by
  apply le_antisymm
  · have := coreness_le_traj (G := worstGraph N) (N - 3) u
    rw [traj_worstGraph hN] at this
    unfold worstTraj at this; split_ifs at this <;> omega
  · refine le_coreness_of_isCoreSet (S := univ) (fun w _ => ?_) (mem_univ u)
    have : #{v ∈ (univ : Finset (Fin N)) | (worstGraph N).Adj w v} = (worstGraph N).degree w := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]; congr 1; ext; simp
    rw [this, worstGraph_degree hN]; split_ifs <;> omega

/-- **The worst-case family of Fig. 3** needs exactly `N − 3` synchronous update steps. With the
paper's convention (execution time = number of update steps + 1, the last round producing no
change) this is `N − 2` rounds, not `N − 1` as claimed in the paper. -/
theorem stab_worstGraph {N : ℕ} (hN : 5 ≤ N) : stab (worstGraph N) = N - 3 := by
  apply le_antisymm
  · apply stab_le_of_traj_eq
    funext u
    rw [traj_worstGraph hN, coreness_worstGraph hN]
    have := u.isLt
    unfold worstTraj; split_ifs <;> omega
  · refine le_of_not_gt fun hlt => ?_
    have h1 := congrFun (traj_eq_coreness_of_le (G := worstGraph N) (s := N - 4) (by omega))
      ⟨N - 2, by omega⟩
    rw [traj_worstGraph hN, coreness_worstGraph hN] at h1
    dsimp only at h1; unfold worstTraj at h1; split_ifs at h1 <;> omega

/-! ### The linear chain -/

section Path

open SimpleGraph

instance (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

theorem card_eq_one_of_val {N : ℕ} (s : Finset (Fin N)) (x : ℕ) (hx : x < N)
    (hs : ∀ v : Fin N, v ∈ s ↔ v.val = x) : #s = 1 := by
  rw [card_eq_one]
  refine ⟨⟨x, hx⟩, ?_⟩
  ext v; rw [hs]; simp [Fin.ext_iff]

theorem pathGraph_degree {N : ℕ} (hN : 2 ≤ N) (u : Fin N) :
    (pathGraph N).degree u = if u.val = 0 ∨ u.val = N - 1 then 1 else 2 := by
  have hu := u.isLt
  rw [← card_neighborFinset_eq_degree]
  have mem : ∀ v : Fin N, v ∈ (pathGraph N).neighborFinset u ↔
      u.val + 1 = v.val ∨ v.val + 1 = u.val := fun v => by
    rw [mem_neighborFinset, pathGraph_adj]
  split_ifs with h
  · rcases h with h | h
    · exact card_eq_one_of_val _ 1 (by omega) fun v => by rw [mem]; omega
    · exact card_eq_one_of_val _ (N - 2) (by omega) fun v => by rw [mem]; omega
  · exact card_eq_two_of_val _ (u.val - 1) (u.val + 1) (by omega) (by omega) (by omega)
      fun v => by rw [mem]; omega

/-- The synchronous trajectory on the path: node `a` keeps estimate `2` while `s` is smaller than
its distance `min a (N − 1 − a)` to the nearest endpoint, and has estimate `1` afterwards. -/
def pathTraj (N s a : ℕ) : ℕ := if s < min a (N - 1 - a) then 2 else 1

theorem traj_pathGraph {N : ℕ} (hN : 2 ≤ N) (s : ℕ) (u : Fin N) :
    traj (pathGraph N) s u = pathTraj N s u.val := by
  induction s generalizing u with
  | zero =>
    rw [traj_zero, pathGraph_degree hN]
    unfold pathTraj; split_ifs <;> omega
  | succ s ih =>
    have hfun : traj (pathGraph N) s = fun v => pathTraj N s v.val := funext ih
    have hu := u.isLt
    have hdeg := pathGraph_degree hN u
    have cast_le : ∀ (i : ℕ) (v : Fin N), ((i : ℕ∞) ≤ toE (fun w : Fin N => pathTraj N s w.val) v
        ↔ i ≤ pathTraj N s v.val) := fun i v => Nat.cast_le
    have cast_lt : ∀ (i : ℕ) (v : Fin N), (toE (fun w : Fin N => pathTraj N s w.val) v < (i : ℕ∞)
        ↔ pathTraj N s v.val < i) := fun i v => Nat.cast_lt
    have h1 : 1 ≤ hIndex (pathGraph N) (toE fun v => pathTraj N s v.val) u :=
      le_hIndex_of_forall_adj (fun v _ => (cast_le 1 v).2 (by unfold pathTraj; split_ifs <;> omega))
        (by rw [hdeg]; split_ifs <;> omega)
    have hk : 1 ≤ pathTraj N s u.val := by unfold pathTraj; split_ifs <;> omega
    have hle := (hIndex_le_degree (G := pathGraph N)
        (toE fun v => pathTraj N s v.val) u).trans_eq hdeg
    rw [traj_succ_apply, hfun]
    beta_reduce
    rw [computeIndex_eq_min' hk h1]
    by_cases hs : s + 1 < min u.val (N - 1 - u.val)
    · have h2 : 2 ≤ hIndex (pathGraph N) (toE fun v => pathTraj N s v.val) u := by
        refine le_hIndex_of_forall_adj (fun v huv => ?_) (by rw [hdeg]; split_ifs <;> omega)
        rw [cast_le]
        rw [pathGraph_adj] at huv
        have := v.isLt
        unfold pathTraj; split_ifs <;> omega
      generalize hIndex (pathGraph N) (toE fun v => pathTraj N s v.val) u = H at *
      unfold pathTraj; split_ifs at hle ⊢ <;> omega
    · by_cases hcur : s < min u.val (N - 1 - u.val)
      · have hlt : hIndex (pathGraph N) (toE fun v => pathTraj N s v.val) u < 2 := by
          by_cases ha : u.val ≤ N - 1 - u.val
          · refine hIndex_lt_of_adj (v := ⟨u.val - 1, by omega⟩) ?_ ?_
              (by rw [hdeg]; split_ifs <;> omega)
            · rw [pathGraph_adj]; dsimp only; omega
            · rw [cast_lt]; dsimp only; unfold pathTraj; split_ifs <;> omega
          · refine hIndex_lt_of_adj (v := ⟨u.val + 1, by omega⟩) ?_ ?_
              (by rw [hdeg]; split_ifs <;> omega)
            · rw [pathGraph_adj]; dsimp only; omega
            · rw [cast_lt]; dsimp only; unfold pathTraj; split_ifs <;> omega
        generalize hIndex (pathGraph N) (toE fun v => pathTraj N s v.val) u = H at *
        unfold pathTraj; split_ifs; omega
      · generalize hIndex (pathGraph N) (toE fun v => pathTraj N s v.val) u = H at *
        unfold pathTraj; split_ifs; omega

/-- On a path with at least two nodes every node has coreness `1`. -/
theorem coreness_pathGraph {N : ℕ} (hN : 2 ≤ N) (u : Fin N) : coreness (pathGraph N) u = 1 := by
  apply le_antisymm
  · have hc := coreness_le_traj (G := pathGraph N) ((N - 1) / 2) u
    rw [traj_pathGraph hN] at hc
    have := u.isLt
    unfold pathTraj at hc; split_ifs at hc <;> omega
  · have hu := u.isLt
    by_cases h : u.val + 1 < N
    · exact one_le_coreness_of_adj (v := ⟨u.val + 1, h⟩) (by rw [pathGraph_adj]; dsimp only; omega)
    · exact one_le_coreness_of_adj (v := ⟨u.val - 1, by omega⟩)
        (by rw [pathGraph_adj]; dsimp only; omega)

/-- **The linear chain** (remark after the analysis of Fig. 3): a path on `N` nodes needs exactly
`⌊(N − 1)/2⌋` update steps, i.e. `⌈N/2⌉` rounds with the paper's convention (steps + 1), as the
paper claims. -/
theorem stab_pathGraph (N : ℕ) : stab (pathGraph N) = (N - 1) / 2 := by
  rcases (by omega : N = 0 ∨ N = 1 ∨ 2 ≤ N) with rfl | rfl | hN
  · exact Nat.le_zero.1 (stab_le_of_traj_eq (funext fun u => u.elim0))
  · have h1 := stab_le_card_sub_minDegree (G := pathGraph 1)
    have h2 := one_le_numMinDegree (G := pathGraph 1)
    rw [Fintype.card_fin] at h1
    omega
  · apply le_antisymm
    · apply stab_le_of_traj_eq
      funext u
      rw [traj_pathGraph hN, coreness_pathGraph hN]
      have := u.isLt
      unfold pathTraj; split_ifs <;> omega
    · refine le_of_not_gt fun hlt => ?_
      have h1 := congrFun (traj_eq_coreness_of_le (G := pathGraph N) (s := (N - 1) / 2 - 1)
        (by omega)) ⟨(N - 1) / 2, by omega⟩
      rw [traj_pathGraph hN, coreness_pathGraph hN] at h1
      dsimp only at h1
      unfold pathTraj at h1; split_ifs at h1 <;> omega

end Path

/-! ### The example of Fig. 2 -/

section Fig2

/-- Edges of Fig. 2 on 0-based labels (`a` is the paper's node `a + 1`):
`1-2, 2-3, 2-4, 3-4, 3-5, 4-5, 5-6`. -/
def fig2E (a b : ℕ) : Prop :=
  (a, b) ∈ [(0, 1), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (4, 5)]

instance (a b : ℕ) : Decidable (fig2E a b) := by unfold fig2E; infer_instance

/-- The six-node graph of Fig. 2. -/
def fig2Graph : SimpleGraph (Fin 6) where
  Adj i j := fig2E i.val j.val ∨ fig2E j.val i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by unfold fig2E; decide⟩

instance : DecidableRel fig2Graph.Adj := fun i j =>
  inferInstanceAs (Decidable (fig2E i.val j.val ∨ fig2E j.val i.val))

/-- `hIndex` of a natural-number estimate vector, without `ℕ∞` (convenient for `decide`). -/
theorem hIndex_toE {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → ℕ) (u : V) :
    hIndex G (toE c) u =
      Nat.findGreatest (fun i => i ≤ #{v ∈ G.neighborFinset u | i ≤ c v}) (G.degree u) := by
  simp only [hIndex, nbrCount, toE, Nat.cast_le]

theorem step_eq_findGreatest {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → ℕ) :
    step G c = fun u => if c u = 0 then 0 else max 1 (min (c u)
      (Nat.findGreatest (fun i => i ≤ #{v ∈ G.neighborFinset u | i ≤ c v}) (G.degree u))) := by
  funext u
  rw [step, computeIndex_eq, hIndex_toE]

theorem fig2_traj_zero : traj fig2Graph 0 = ![1, 3, 3, 3, 3, 1] := by
  funext u; rw [traj_zero]; revert u; decide

theorem fig2_traj_one : traj fig2Graph 1 = ![1, 2, 3, 3, 2, 1] := by
  rw [traj_succ, fig2_traj_zero, step_eq_findGreatest]; funext u; revert u; decide

theorem fig2_traj_two : traj fig2Graph 2 = ![1, 2, 2, 2, 2, 1] := by
  rw [traj_succ, fig2_traj_one, step_eq_findGreatest]; funext u; revert u; decide

/-- The corenesses in Fig. 2: nodes `1` and `6` have coreness `1`, nodes `2`–`5` coreness `2`. -/
theorem coreness_fig2 : coreness fig2Graph = ![1, 2, 2, 2, 2, 1] := by
  funext u
  apply le_antisymm
  · have := coreness_le_traj (G := fig2Graph) 2 u
    rwa [fig2_traj_two] at this
  · have hS : IsCoreSet fig2Graph 2 {1, 2, 3, 4} := by decide
    fin_cases u
    · exact one_le_coreness_of_adj (v := 1) (by decide)
    · exact le_coreness_of_isCoreSet hS (by decide)
    · exact le_coreness_of_isCoreSet hS (by decide)
    · exact le_coreness_of_isCoreSet hS (by decide)
    · exact le_coreness_of_isCoreSet hS (by decide)
    · exact one_le_coreness_of_adj (v := 4) (by decide)

/-- Fig. 2 needs `2` update steps (the paper's three rounds, the last of which changes nothing). -/
theorem stab_fig2 : stab fig2Graph = 2 := by
  apply le_antisymm
  · exact stab_le_of_traj_eq (fig2_traj_two.trans coreness_fig2.symm)
  · refine le_of_not_gt fun hlt => ?_
    have h := traj_eq_coreness_of_le (G := fig2Graph) (s := 1) (by omega)
    rw [fig2_traj_one, coreness_fig2] at h
    have := congrFun h 2
    simp at this

end Fig2

end KCoreDecomposition
