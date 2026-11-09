import Papers.PODC2016.BCCConnectivitySketches.Pruning
import Papers.PODC2016.BCCConnectivitySketches.Cycles

/-!
# One-round connectivity in `BClique_r` (Theorem 3)

Model `BClique_r[b]`: as `BClique[b]`, but node `v`'s input is the subgraph induced by its
radius-`r` ball (`localView G r v`). Protocol: `v` computes its row of `G̃` (delete the
maximal edge, w.r.t. a fixed edge order, of every cycle of length `≤ 2r`); this is possible
locally (`isHeavy_localView_iff`). Then all nodes run the one-round `s`-pruning protocol on `G̃`
with `s = degBound n r`, the least `s` with `n ≤ s^r` (so `s < n^{1/r} + 1`). `G̃` has girth
`> 2r` (`prunedGraph_noShortCycles`) hence is `s`-degenerate (`proposition_2`), so the pruning
reconstructs all of `G̃` (`reconstruct_degenerate`); any spanning forest of `G̃` is one of `G`
(`proposition_1`).
-/

namespace Podc.BCCConnectivitySketches

open Finset Cslib.CongestedClique

/-- The edge order of the proof of Theorem 3: `{u, v}` with `u < v` has rank `u·n + v`, i.e. the
lexicographic order on `(min, max)`. -/
def lexRank (n : ℕ) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun a b => min (a : ℕ) b * n + max (a : ℕ) b, fun a b => by
    simp only; rw [min_comm, max_comm]⟩

lemma lexRank_injective (n : ℕ) : Function.Injective (lexRank n) := by
  intro e f h
  induction e using Sym2.ind with
  | h a b =>
  induction f using Sym2.ind with
  | h c d =>
  simp only [lexRank, Sym2.lift_mk] at h
  have hmx : ∀ x y : Fin n, max (x : ℕ) y < n := fun x y => max_lt x.2 y.2
  have key : ∀ x y : ℕ, x < n → (y * n + x) / n = y ∧ (y * n + x) % n = x := by
    intro x y hx
    constructor
    · rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hx, zero_add]
    · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have h1 : min (a : ℕ) b = min (c : ℕ) d := by
    rw [← (key (max (a : ℕ) b) (min (a : ℕ) b) (hmx a b)).1, h, (key _ _ (hmx c d)).1]
  have h2 : max (a : ℕ) b = max (c : ℕ) d := by
    rw [← (key (max (a : ℕ) b) (min (a : ℕ) b) (hmx a b)).2, h, (key _ _ (hmx c d)).2]
  rw [Sym2.eq_iff]
  simp only [Fin.ext_iff]
  omega

/-- The degeneracy bound: the least `s` with `n ≤ s^r`. -/
noncomputable def degBound (n r : ℕ) : ℕ := by
  classical
  exact if h : ∃ s, n ≤ s ^ r then Nat.find h else n

lemma degBound_spec {n r : ℕ} (hr : 1 ≤ r) : n ≤ degBound n r ^ r := by
  have h : ∃ s, n ≤ s ^ r := ⟨n, Nat.le_self_pow (by omega) n⟩
  classical
  rw [degBound, dite_eq_left_of_eq_true (eq_true h)]
  exact Nat.find_spec h

/-- `s = degBound n r < n^{1/r} + 1`, so the messages of Theorem 3 have `O(n^{1/r} log n)` bits. -/
lemma degBound_lt {n r : ℕ} (hr : 1 ≤ r) : (degBound n r : ℝ) < (n : ℝ) ^ (1 / (r : ℝ)) + 1 := by
  have h : ∃ s, n ≤ s ^ r := ⟨n, Nat.le_self_pow (by omega) n⟩
  classical
  have hd : degBound n r = Nat.find h := by rw [degBound, dite_eq_left_of_eq_true (eq_true h)]
  rcases Nat.eq_zero_or_pos (degBound n r) with h0 | hpos
  · rw [h0]; push_cast; positivity
  · have hlt : n > (degBound n r - 1) ^ r := by
      have := Nat.find_min h (m := degBound n r - 1) (by rw [← hd]; omega)
      omega
    have hr' : (0 : ℝ) < 1 / (r : ℝ) := by positivity
    have key : ((degBound n r - 1 : ℕ) : ℝ) < (n : ℝ) ^ (1 / (r : ℝ)) := by
      have e : ((degBound n r - 1 : ℕ) : ℝ) =
          (((degBound n r - 1 : ℕ) : ℝ) ^ r) ^ (1 / (r : ℝ)) := by
        rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
      rw [e]
      exact Real.rpow_lt_rpow (by positivity) (by exact_mod_cast hlt) hr'
    have : (degBound n r : ℝ) = ((degBound n r - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hpos]; ring
    linarith

/-- Node `v`'s row of `G̃`, computed from its local view `H`. -/
noncomputable def tildeRow {n : ℕ} (r : ℕ) (v : Fin n) (H : SimpleGraph (Fin n)) : Finset (Fin n) := by
  classical
  exact univ.filter fun u => H.Adj v u ∧ ¬ IsHeavy H r (lexRank n) s(v, u)

lemma tildeRow_localView {n r : ℕ} (hr : 1 ≤ r) (G : SimpleGraph (Fin n)) (v : Fin n) :
    tildeRow r v (localView G r v) = nbrs (prunedGraph G r (lexRank n)) v := by
  ext u
  simp only [tildeRow, mem_filter, mem_univ, true_and, mem_nbrs, prunedGraph,
    SimpleGraph.deleteEdges_adj, Set.mem_ofPred_eq, localView_adj_iff hr,
    isHeavy_localView_iff (Sym2.mem_mk_left v u)]

/-- The protocol of Theorem 3 (typed). -/
noncomputable def connAlg (n r : ℕ) :
    TAlg (Fin n) (SimpleGraph (Fin n))
      (SimpleGraph (Fin n) × Option (List (Fin n) × Finset (Sym2 (Fin n)))) (PMsg n (degBound n r)) :=
  TAlg.oneRound (fun v H => pruneMsg n (degBound n r) v (tildeRow r v H)) (pruneDec n (degBound n r))

/-- The protocol of Theorem 3 in `BClique_r[pruneBits n s]`, `s = degBound n r`. -/
noncomputable def connBcast (n r : ℕ) :
    Bcast.Algorithm (Fin n) (SimpleGraph (Fin n))
      (SimpleGraph (Fin n) × Option (List (Fin n) × Finset (Sym2 (Fin n))))
      (pruneBits n (degBound n r)) :=
  (connAlg n r).toBits _ (card_pmsg n _)

/-- Final local computation: a fixed spanning forest of the reconstructed graph. -/
noncomputable def forestOf {n : ℕ} (E : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  (exists_isSpanningForest (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n))))).choose

/-- **Theorem 3** of [Montealegre–Todinca]: for `r ≥ 1` there is a deterministic one-round protocol
in `BClique_r[pruneBits n s]`, `s = degBound n r < n^{1/r} + 1` (so `O(n^{1/r} log n)` bits, see
`theorem_3_bits`), after which every node outputs a spanning forest of the input graph. -/
theorem theorem_3 (n r : ℕ) (hr : 1 ≤ r) :
    ∃ (σ : Type) (A : Bcast.Algorithm (Fin n) (SimpleGraph (Fin n)) σ (pruneBits n (degBound n r)))
      (out : σ → SimpleGraph (Fin n)),
      ∀ (G : SimpleGraph (Fin n)) (v : Fin n),
        IsSpanningForest G (out (A.run (fun u => localView G r u) 1 v)) := by
  classical
  refine ⟨_, connBcast n r, fun st => forestOf (st.2.getD ([], ∅)).2, fun G v => ?_⟩
  set Gt := prunedGraph G r (lexRank n)
  have hrun : (connBcast n r).run (fun u => localView G r u) 1 v =
      (localView G r v, some (pruneDec n (degBound n r)
        fun w => pruneMsg n (degBound n r) w (nbrs Gt w))) := by
    rw [connBcast, TAlg.run_toBits]
    simp only [connAlg, TAlg.oneRound_run, tildeRow_localView hr]
    rfl
  rw [hrun]
  simp only [Option.getD_some]
  obtain ⟨hP, hE⟩ := pruneDec_spec (d := degBound n r) Gt
  have hdeg : Podc.CongestedCliquePower.IsDegenerate Gt (degBound n r) :=
    proposition_2 hr prunedGraph_noShortCycles _ (by simpa using degBound_spec (n := n) hr)
  have hrec := reconstruct_degenerate hdeg hP hE
  set E := (pruneDec n (degBound n r) fun w => pruneMsg n (degBound n r) w (nbrs Gt w)).2
  have hF : IsSpanningForest (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))) (forestOf E) :=
    (exists_isSpanningForest _).choose_spec
  rw [hrec, SimpleGraph.fromEdgeSet_edgeSet] at hF
  exact IsSpanningForest.of_prunedGraph (lexRank_injective n) hF

/-- Message size of Theorem 3: `pruneBits n s ≤ (2s + 2)⌈log₂(n+1)⌉ + 1` with
`s < n^{1/r} + 1`, i.e. `O(n^{1/r} log n)`. -/
theorem theorem_3_bits {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) :
    pruneBits n (degBound n r) ≤ (2 * degBound n r + 2) * Nat.clog 2 (n + 1) + 1 ∧
      (degBound n r : ℝ) < (n : ℝ) ^ (1 / (r : ℝ)) + 1 :=
  ⟨pruneBits_le hn _, degBound_lt hr⟩

end Podc.BCCConnectivitySketches
