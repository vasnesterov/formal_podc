import Papers.PODC2021.AllYouNeedIsDAG.Safety

/-!
# Lemma 1 is false for indirectly committed leaders

Lemma 1 of the paper: "If some process `p_i` commits the leader vertex `v` of a wave `w`, then for
every leader vertex `u` of a wave `w' > w` and for every process `p_j`, if
`u ∈ DAG_j[round(w', 1)]`, then `strong_path(u, v)` returns true in wave `w'`." Here *commits*
means "pops from the stack" (Section 6.1), which includes leaders committed *indirectly* through
the loop of lines 39–43. The proof only treats leaders committed by the commit rule of line 36.

Counterexample (`n = 4`, `f = 1`, all vertices present, no weak edges, coin = process `0` in every
wave). The observer is the correct process `3`; when wave `w` becomes ready its local DAG contains
all vertices of rounds `1..4w` except its own `(4w, 3)` (not yet delivered back to it). This view is
realizable: the round-`(4w+1)` vertex that process `3` then creates has strong edges exactly to
the round-`4w` vertices of this DAG (`realizable`).

* wave 1: only `(4,0)` of round 4 reaches the leader `v₁ = (1,0)` — no commit;
* wave 2: the leader `v₂ = (5,0)` has strong edges to `(4,1), (4,2), (4,3)` only, so it has **no
  strong path to `v₁`**; only `(8,0)` reaches it — no commit;
* wave 3: the three round-12 vertices of its DAG reach `v₃ = (9,0)` — direct commit; `v₃` reaches `v₁` (via
  `(5,1) → (4,0)`) but not `v₂`, so the process pushes `v₁`, i.e. **commits `v₁`** (indirectly)
  together with `v₃`.

So `v₁` is committed, `v₂` is a leader of a later wave in the DAG of the same process, and
`strong_path(v₂, v₁)` is false. Total order is *not* affected (see `Safety.lean`, where Lemma 1
is proved for direct commits, which is all the total-order argument needs).
-/

namespace DagRider.Lemma1Counterexample

open Finset

/-- Strong edges of the counterexample. -/
def strongCE : Vtx (Fin 4) → Finset (Fin 4)
  | (r, s) =>
    if r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 6 ∨ r = 7 ∨ r = 8 then (if s = 0 then {0, 1, 2} else {1, 2, 3})
    else if r = 5 ∨ r = 9 then (if s = 0 then {1, 2, 3} else {0, 1, 2})
    else {0, 1, 2}

/-- The global contents (blocks are irrelevant). -/
def C : Content (Fin 4) Unit := ⟨strongCE, fun _ => ∅, fun _ => ()⟩

/-- The coin always elects process `0`. -/
def coin : ℕ → Fin 4 := fun _ => 0

/-- The local DAG of process `3` when wave `w` is ready: all vertices of rounds `1..4w` except
its own vertex `(4w, 3)`. -/
def D (w : ℕ) : Finset (Vtx (Fin 4)) := ((Finset.Icc 1 (4 * w)) ×ˢ Finset.univ).erase (4 * w, 3)

lemma D_closed (w : ℕ) : Closed C (D w) := by
  intro v hv u ⟨he, hu⟩
  simp only [D, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
    and_true] at hv ⊢
  rcases he with ⟨h, -⟩ | h
  · refine ⟨fun h' => ?_, by omega⟩
    rw [h'] at h; simp at h; omega
  · simp [C] at h

lemma D_valid (w : ℕ) : Valid 1 C (D w) := by
  intro v _
  obtain ⟨r, s⟩ := v
  simp only [C, strongCE]
  split_ifs <;> decide

/-- No commit in waves 1 and 2, direct commit of `v₃` in wave 3 whose chain contains `v₁`. -/
lemma facts :
    leader coin (D 1) 1 = some (1, 0) ∧ commitCount C (D 1) (1, 0) 1 = 1 ∧
    leader coin (D 2) 2 = some (5, 0) ∧ commitCount C (D 2) (5, 0) 2 = 1 ∧
    leader coin (D 3) 3 = some (9, 0) ∧ commitCount C (D 3) (9, 0) 3 = 3 ∧
    chain C coin (D 3) (9, 0) (wavesDown 3 0) = [(1, 0)] ∧
    ¬ SPath C (5, 0) (1, 0) := by
  decide +kernel

/-- The snapshots are views a correct process `3` can have: the vertex `(4w+1, 3)` it creates at
`wave_ready(w)` has strong edges exactly to the round-`4w` vertices of its DAG (line 19). -/
lemma realizable : ∀ w ∈ [1, 2, 3],
    ((D w).filter (fun v => v.1 = 4 * w)).image Prod.snd = C.strong (4 * w + 1, 3) := by
  decide +kernel

/-- **Lemma 1 (as stated, for all committed leaders) is false.** The process directly commits the
leader of wave 3 with `decidedWave = 0`; its stack is `[v₃, v₁]`, so it commits `v₁ = (1,0)`, the
leader of wave 1. The leader `v₂ = (5,0)` of the later wave 2 is in its DAG, but has no strong path
to `v₁`. -/
theorem lemma1_false (sortV : Finset (Vtx (Fin 4)) → List (Vtx (Fin 4))) :
    (∀ w, Closed C (D w) ∧ Valid 1 C (D w)) ∧ (∀ w, D w ⊆ D (w + 1)) ∧
    (∀ w ∈ [1, 2, 3], ((D w).filter (fun v => v.1 = 4 * w)).image Prod.snd =
      C.strong (4 * w + 1, 3)) ∧
    (orun 1 C coin sortV D 2).decided = 0 ∧
    (orun 1 C coin sortV D 3).decided = 3 ∧
    (orun 1 C coin sortV D 3).delivered =
      deliverAll C sortV (D 3) [] [(1, 0), (9, 0)] ∧
    leader coin (D 3) 2 = some (5, 0) ∧ ¬ SPath C (5, 0) (1, 0) := by
  obtain ⟨h1, h1c, h2, h2c, h3, h3c, hch, hno⟩ := facts
  have hD2 : leader coin (D 3) 2 = some (5, 0) := by decide
  have o1 : orun 1 C coin sortV D 1 = ⟨0, []⟩ := by
    simp only [orun, waveReady, h1, h1c]; rfl
  have o2 : orun 1 C coin sortV D 2 = ⟨0, []⟩ := by
    simp only [orun] at o1 ⊢; rw [o1]; simp only [waveReady, h2, h2c]; rfl
  refine ⟨fun w => ⟨D_closed w, D_valid w⟩, ?_, realizable, by rw [o2], ?_, ?_, hD2, hno⟩
  · intro w x hx
    obtain ⟨a, b⟩ := x
    simp only [D, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
      and_true, ne_eq, Prod.mk.injEq] at hx ⊢
    omega
  · simp only [orun] at o2 ⊢; rw [o2]; simp only [waveReady, h3, h3c]; rfl
  · simp only [orun] at o2 ⊢; rw [o2]; simp only [waveReady, h3, h3c, hch]; rfl

end DagRider.Lemma1Counterexample
