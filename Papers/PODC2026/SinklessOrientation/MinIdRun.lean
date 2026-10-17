import Papers.PODC2026.SinklessOrientation.MinId
import Cslib.Computability.Distributed.Local.LocallyIterative

/-!
# Theorem 2.1 as an explicit `k`-round flooding algorithm

The proof of Theorem 2.1 of [Nolin, PODC'26]: "For `k` rounds, each node broadcasts to its
neighbors the smallest identifier it knows about (its own included). At the end of the `k` rounds,
each node knows the smallest identifier in its inclusive distance-`k` neighborhood. It also knows
its distance to that node, which is simply the round in which it learned the identifier."

We implement this as a CSLib locally-iterative algorithm (`Cslib.LocallyIterative.Algorithm`):
the state of a node is `(ID, m, d)` (own identifier, smallest identifier known so far, round in
which it was learned). In every round a node only uses the *set* of its neighbours' states, so the
algorithm is a broadcast algorithm.

## Main results

* `minId_succ`: `m_{t+1}(v) = min (m_t(v), min_{w ∈ N(v)} m_t(w))`.
* `floodAlg_run`: after `t` rounds, node `v` is in state `(ID_v, m_v, d_v)` for radius `t`.
* `floodAlg_orientation`, `theorem_2_1` (**Theorem 2.1**): after `k` rounds, the orientation
  `minIdOrientation` of an edge is obtained by comparing the final states of its endpoints
  (one more exchange), and it is `k`-sinksparse.

No finiteness assumption on the graph (or local finiteness) is needed: all infima are infima of
nonempty sets of natural numbers.
-/

namespace SinklessOrientation

open SimpleGraph Cslib.LocallyIterative

variable {V : Type*} {G : SimpleGraph V} {id : V → ℕ}

/-! ### The `minId` recursion -/

lemma minId_mono {v : V} {s t : ℕ} (h : s ≤ t) : minId G id t v ≤ minId G id s v := by
  obtain ⟨u, hu, hid⟩ := minId_spec (G := G) (id := id) (k := s) v
  exact hid ▸ minId_le (closedBall_mono (Nat.cast_le.2 h) hu)

/-- `m_{t+1}(v)` is the minimum of `m_t(v)` and of the `m_t(w)` of the neighbours `w` of `v`. -/
lemma minId_succ (t : ℕ) (v : V) :
    minId G id (t + 1) v =
      sInf (insert (minId G id t v) ((fun w => minId G id t w) '' G.neighborSet v)) := by
  apply le_antisymm
  · apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro x (rfl | ⟨w, hw, rfl⟩)
    · exact minId_mono (Nat.le_succ t)
    · obtain ⟨u, hu, hid⟩ := minId_spec (G := G) (id := id) (k := t) w
      exact (minId_le (mem_closedBall_succ_iff.2 (Or.inr ⟨w, hw, hu⟩))).trans hid.le
  · obtain ⟨u, hu, hid⟩ := minId_spec (G := G) (id := id) (k := t + 1) v
    rw [← hid]
    rcases mem_closedBall_succ_iff.1 hu with hu | ⟨w, hw, hu⟩
    · exact (Nat.sInf_le (Set.mem_insert _ _)).trans (minId_le hu)
    · exact (Nat.sInf_le (Set.mem_insert_of_mem (minId G id t v)
        (Set.mem_image_of_mem (fun w => minId G id t w) hw))).trans (minId_le hu)

/-! ### The flooding algorithm -/

/-- The flooding algorithm of the proof of Theorem 2.1. The state of a node is `(ID, m, d)`: its
own identifier, the smallest identifier it knows about, and the round in which it learned it
(= its distance to the node with that identifier). In round `t`, a node in state `(i, m, d)` whose
neighbours are in the states `N` computes `m' = min (m, min {m_u | (_, m_u, _) ∈ N})` and moves to
`(i, m', if m' < m then t + 1 else d)`.

States are three natural numbers `≤ max (ID_max, k)` during the first `k` rounds, i.e. `O(log n)`
bits when identifiers are `poly(n)` and `k ≤ n`; a node sends the same message (its state) to all
its neighbours and only uses the *set* of received states, so every round is a CONGEST broadcast
round. -/
noncomputable def floodAlg : Algorithm (ℕ × ℕ × ℕ) :=
  ⟨fun t x N =>
    let m' := sInf (insert x.2.1 ((fun s => s.2.1) '' N))
    (x.1, m', if m' < x.2.1 then t + 1 else x.2.2)⟩

lemma floodAlg_step (t : ℕ) (x : ℕ × ℕ × ℕ) (N : Set (ℕ × ℕ × ℕ)) :
    floodAlg.step t x N =
      (x.1, sInf (insert x.2.1 ((fun s => s.2.1) '' N)),
        if sInf (insert x.2.1 ((fun s => s.2.1) '' N)) < x.2.1 then t + 1 else x.2.2) := rfl

/-- Initial state of `v`: `(ID_v, ID_v, 0)`. -/
def floodInit (id : V → ℕ) (v : V) : ℕ × ℕ × ℕ := (id v, id v, 0)

variable (G) in
/-- After `t` rounds of `floodAlg`, every node `v` is in state `(ID_v, m_v, d_v)` (radius `t`):
it knows the smallest identifier within distance `t` and its distance to the node carrying it. -/
theorem floodAlg_run (hid : Function.Injective id) (t : ℕ) (v : V) :
    floodAlg.run G (floodInit id) t v = (id v, minId G id t v, minDist G id t v) := by
  induction t generalizing v with
  | zero =>
    have hm : minId G id 0 v = id v := by
      apply le_antisymm (minId_le_id v)
      obtain ⟨u, hu, hu'⟩ := minId_spec (G := G) (id := id) (k := 0) v
      simp only [mem_cball, Nat.cast_zero, nonpos_iff_eq_zero, edist_eq_zero_iff] at hu
      rw [← hu', ← hu]
    have hl : leader G id 0 v = v := leader_eq hid hm.symm
    simp [floodInit, hm, minDist, hl]
  | succ t ih =>
    have hrun : floodAlg.run G (floodInit id) t = fun v => (id v, minId G id t v, minDist G id t v) :=
      funext ih
    have hN : (fun s : ℕ × ℕ × ℕ => s.2.1) '' nbrColors G (floodAlg.run G (floodInit id) t) v =
        (fun w => minId G id t w) '' G.neighborSet v := by
      rw [nbrColors, Set.image_image, hrun]
    rw [Algorithm.run_succ_apply, floodAlg_step, hN, ih]
    simp only
    rw [← minId_succ]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only
    split_ifs with hlt
    · -- a new, smaller identifier was learned in round `t + 1`: its node is at distance `t + 1`
      obtain ⟨hL, hLid⟩ := leader_spec (G := G) (id := id) (k := t + 1) v
      have hnot : leader G id (t + 1) v ∉ cball G v t := fun h =>
        absurd (minId_le (id := id) h) (by rw [hLid]; omega)
      have hd := edist_leader (G := G) (id := id) (k := t + 1) v
      have h1 : G.edist v (leader G id (t + 1) v) ≤ (t + 1 : ℕ) := mem_cball.1 hL
      have h2 : ¬ G.edist v (leader G id (t + 1) v) ≤ t := fun h => hnot (mem_cball.2 h)
      rw [hd] at h1 h2
      have h1' : minDist G id (t + 1) v ≤ t + 1 := by exact_mod_cast h1
      have h2' : ¬ minDist G id (t + 1) v ≤ t := by exact_mod_cast h2
      omega
    · -- the smallest known identifier did not change, nor did the node carrying it
      have heq : minId G id (t + 1) v = minId G id t v :=
        le_antisymm (minId_mono (Nat.le_succ t)) (not_lt.1 hlt)
      have hl : leader G id (t + 1) v = leader G id t v :=
        leader_eq hid ((leader_spec v).2.trans heq.symm)
      simp only [minDist, hl]

/-- Reorder a state `(ID, m, d)` into the key `(m, d, ID)`. -/
def reorder (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.2.1, x.2.2, x.1)

variable (G) in
lemma reorder_floodAlg_run (hid : Function.Injective id) (t : ℕ) (v : V) :
    reorder (floodAlg.run G (floodInit id) t v) = key G id t v := by
  rw [floodAlg_run G hid]; rfl

variable (G) in
/-- **Theorem 2.1** of [Nolin, PODC'26]: a `k`-sinksparse orientation in `k (+1)` rounds of
CONGEST. After exactly `k` rounds of the flooding algorithm `floodAlg`, the direction of every
edge `uv` of `minIdOrientation` is determined by comparing the final states of `u` and `v`
(one more exchange): the edge points towards the smaller key `(m, d, ID)`. -/
theorem floodAlg_orientation (k : ℕ) (hid : Function.Injective id) (u v : V) :
    (minIdOrientation G id k hid).out u v ↔
      G.Adj u v ∧ keyLt (reorder (floodAlg.run G (floodInit id) k v))
        (reorder (floodAlg.run G (floodInit id) k u)) := by
  rw [reorder_floodAlg_run G hid, reorder_floodAlg_run G hid]
  rfl

variable (G) in
/-- **Theorem 2.1** of [Nolin, PODC'26]: a `k`-sinksparse orientation in `k (+1)` rounds of
CONGEST. The orientation obtained by running the flooding algorithm `floodAlg` for `k` rounds and
then orienting each edge towards the endpoint with the smaller final key `(m, d, ID)` is
`k`-sinksparse (distinct sinks are at distance `> k`). -/
theorem theorem_2_1 (k : ℕ) (hid : Function.Injective id) :
    (minIdOrientation G id k hid).IsSinkSparse k ∧
      ∀ u v, (minIdOrientation G id k hid).out u v ↔
        G.Adj u v ∧ keyLt (reorder (floodAlg.run G (floodInit id) k v))
          (reorder (floodAlg.run G (floodInit id) k u)) :=
  ⟨minIdOrientation_isSinkSparse hid, floodAlg_orientation G k hid⟩

end SinklessOrientation
