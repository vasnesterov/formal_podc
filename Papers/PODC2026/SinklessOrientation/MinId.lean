import Papers.PODC2026.SinklessOrientation.Basic

/-!
# Theorem 2.1: a `k`-sinksparse orientation from the smallest identifier within distance `k`

Every node `v` learns `m_v`, the smallest identifier in its inclusive distance-`k` neighbourhood
(`minId`), and its distance `d_v` to the node with that identifier (`minDist`; that node is
`leader`). An edge `uv` is oriented towards the endpoint with the smaller key
`(m, d, ID)` (lexicographically, `keyLt`). This is `minIdOrientation`.

## Main results

* `minIdOrientation_not_isSink`: a node `v` with `ID_v ≠ m_v` is not a sink.
* `minIdOrientation_isSinkSparse` (**Theorem 2.1**, correctness): the orientation is
  `k`-sinksparse — distinct sinks are at distance `> k`. No finiteness is needed.
* `minIdOrientation_isLocal` (**Theorem 2.1**, locality): the orientation of an edge `uv` only
  depends on the radius-`(k+1)` view of `u`, i.e. it is computed in `k + 1` LOCAL rounds.
  The explicit `k`-round flooding algorithm (with `O(log n)`-bit states, i.e. CONGEST broadcast)
  is in `MinIdRun.lean`.
-/

namespace SinklessOrientation

open SimpleGraph
open Cslib.Local (GAgree)

variable {V : Type*} (G : SimpleGraph V) (id : V → ℕ) (k : ℕ)

/-- `m_v`: the smallest identifier in the inclusive distance-`k` neighbourhood of `v`. -/
noncomputable def minId (v : V) : ℕ := sInf (id '' cball G v k)

/-- The node of the distance-`k` neighbourhood of `v` with the smallest identifier. -/
noncomputable def leader (v : V) : V :=
  @Classical.epsilon V ⟨v⟩ fun u => u ∈ cball G v k ∧ id u = minId G id k v

/-- `d_v`: the distance from `v` to the node with identifier `m_v`. -/
noncomputable def minDist (v : V) : ℕ := G.dist v (leader G id k v)

/-- The key `(m_v, d_v, ID_v)` of a node. -/
noncomputable def key (v : V) : ℕ × ℕ × ℕ := (minId G id k v, minDist G id k v, id v)

/-- The lexicographic order on keys. -/
def keyLt (a b : ℕ × ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1) ∨ (a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)

lemma keyLt_asymm {a b : ℕ × ℕ × ℕ} (h : keyLt a b) : ¬ keyLt b a := by
  unfold keyLt at *; omega

lemma keyLt_or_keyLt {a b : ℕ × ℕ × ℕ} (h : a.2.2 ≠ b.2.2) : keyLt a b ∨ keyLt b a := by
  unfold keyLt; omega

variable {G id k}

lemma minId_spec (v : V) : ∃ u ∈ cball G v k, id u = minId G id k v :=
  Nat.sInf_mem (s := id '' cball G v k) ⟨id v, v, mem_closedBall_self, rfl⟩

lemma minId_le {v u : V} (hu : u ∈ cball G v k) : minId G id k v ≤ id u :=
  Nat.sInf_le ⟨u, hu, rfl⟩

lemma minId_le_id (v : V) : minId G id k v ≤ id v := minId_le mem_closedBall_self

lemma leader_spec (v : V) :
    leader G id k v ∈ cball G v k ∧ id (leader G id k v) = minId G id k v :=
  @Classical.epsilon_spec V _ (minId_spec v)

lemma leader_eq (hid : Function.Injective id) {v u : V} (h : id u = minId G id k v) :
    leader G id k v = u :=
  hid ((leader_spec v).2.trans h.symm)

lemma edist_leader (v : V) : G.edist v (leader G id k v) = minDist G id k v :=
  edist_eq_natCast_dist_of_le (mem_cball.1 (leader_spec v).1)

variable (G id k) in
/-- The orientation of Theorem 2.1: the edge `uv` points from `u` to `v` iff
`(m_v, d_v, ID_v) < (m_u, d_u, ID_u)` lexicographically ("each time towards the smallest value"). -/
noncomputable def minIdOrientation (hid : Function.Injective id) : Orientation G where
  out u v := G.Adj u v ∧ keyLt (key G id k v) (key G id k u)
  adj_of_out _ _ h := h.1
  out_or_out u v h := by
    have hne : (key G id k v).2.2 ≠ (key G id k u).2.2 := fun e => h.ne (hid e).symm
    rcases keyLt_or_keyLt hne with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h.symm, h'⟩
  not_out_of_out _ _ h h' := keyLt_asymm h.2 h'.2

variable (hid : Function.Injective id)

/-- In the proof of Theorem 2.1: "Any node `v` s.t. `ID_v ≠ m_v` is not a sink, since one of its
neighbors `u ∈ N(v)` is closer to the node of identifier `m_v`." -/
theorem minIdOrientation_not_isSink {v : V} (hv : id v ≠ minId G id k v) :
    ¬ (minIdOrientation G id k hid).IsSink v := by
  intro hs
  obtain ⟨hw, hwid⟩ := leader_spec (G := G) (id := id) (k := k) v
  set w := leader G id k v with hw_def
  have hwv : w ≠ v := fun e => hv (e ▸ hwid)
  have hdist : G.edist v w = minDist G id k v := edist_leader v
  -- `d_v ≥ 1`
  obtain ⟨d, hd⟩ : ∃ d, minDist G id k v = d + 1 := by
    rcases Nat.eq_zero_or_eq_succ_pred (minDist G id k v) with h0 | h0
    · rw [h0] at hdist; simp at hdist; exact absurd hdist.symm hwv
    · exact ⟨_, h0⟩
  rw [hd, SimpleGraph.edist_comm] at hdist
  obtain ⟨u, hu, huv⟩ := exists_adj_of_edist_eq_succ hdist
  have hdk : d + 1 ≤ k := by
    have := hw; simp only [mem_cball] at this; rw [edist_comm, hdist] at this
    exact_mod_cast this
  have hwu : w ∈ cball G u k := by
    simp only [mem_cball]; rw [edist_comm, hu]; exact_mod_cast (by omega : d ≤ k)
  have hle : minId G id k u ≤ minId G id k v := hwid ▸ minId_le hwu
  apply hs u
  refine ⟨huv.symm, ?_⟩
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr (Or.inl ⟨heq, ?_⟩)
    have hlu : leader G id k u = w := leader_eq hid (hwid.trans heq.symm)
    have : G.edist u (leader G id k u) = d := by rw [hlu, edist_comm, hu]
    rw [edist_leader] at this
    have h2 : minDist G id k u = d := by exact_mod_cast this
    simp only [key, h2, hd]; omega

/-- Sinks of `minIdOrientation` are exactly local identifier minima: `ID_v = m_v`. -/
theorem id_eq_minId_of_isSink {v : V} (hv : (minIdOrientation G id k hid).IsSink v) :
    id v = minId G id k v := by
  by_contra h; exact minIdOrientation_not_isSink hid h hv

/-- **Theorem 2.1** of [Nolin, PODC'26] (correctness): orienting every edge towards the endpoint
with the lexicographically smaller `(m, d, ID)` gives a `k`-sinksparse orientation: two distinct
sinks are at distance `> k`. -/
theorem minIdOrientation_isSinkSparse : (minIdOrientation G id k hid).IsSinkSparse k := by
  intro u v hu hv huv
  by_contra hlt
  push Not at hlt
  have h1 : minId G id k u ≤ id v := minId_le (mem_cball.2 hlt)
  have h2 : minId G id k v ≤ id u := minId_le (by rw [mem_cball, SimpleGraph.edist_comm]; exact hlt)
  rw [← id_eq_minId_of_isSink hid hu] at h1
  rw [← id_eq_minId_of_isSink hid hv] at h2
  exact huv (hid (le_antisymm h1 h2))

/-! ### Locality -/

section Locality

variable {G' : SimpleGraph V}

lemma key_eq_of_gAgree {v : V} (hA : GAgree G G' v k) : key G' id k v = key G id k v := by
  have hm : minId G' id k v = minId G id k v := by simp only [minId, hA.closedBall_eq le_rfl]
  have hl : leader G' id k v = leader G id k v := by
    simp only [leader, hm, hA.closedBall_eq le_rfl]
  have hd : minDist G' id k v = minDist G id k v := by
    have h1 := edist_leader (G := G') (id := id) (k := k) v
    rw [hl, hA.edist_eq (mem_cball.1 (leader_spec v).1), edist_leader] at h1
    exact_mod_cast h1.symm
  simp only [key, hm, hd]

/-- **Theorem 2.1** of [Nolin, PODC'26] (round complexity): the orientation of the edge `uv` is
determined by the radius-`(k+1)` view of `u` (`k` rounds to learn `(m, d)`, one more to compare
with the neighbours), i.e. it is computable in `k + 1 = O(k)` LOCAL rounds. -/
theorem minIdOrientation_isLocal :
    IsLocal (fun G => minIdOrientation G id k hid) (k + 1) := by
  intro G G' u hA v
  simp only [minIdOrientation]
  have hadj : G.Adj u v ↔ G'.Adj u v := hA.adj_iff (by omega) v
  have hu : key G' id k u = key G id k u := key_eq_of_gAgree (hA.mono_radius (by omega))
  constructor
  · rintro ⟨h, h'⟩
    have hv : key G' id k v = key G id k v :=
      key_eq_of_gAgree (hA.mono (a := 1) (by rw [edist_eq_one_iff_adj.2 h]; simp) (by omega))
    exact ⟨hadj.1 h, by rw [hu, hv]; exact h'⟩
  · rintro ⟨h, h'⟩
    have hv : key G' id k v = key G id k v :=
      key_eq_of_gAgree (hA.mono (a := 1) (by rw [edist_eq_one_iff_adj.2 (hadj.2 h)]; simp)
        (by omega))
    exact ⟨hadj.2 h, by rw [hu, hv] at h'; exact h'⟩

end Locality

end SinklessOrientation
