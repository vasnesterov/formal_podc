import Papers.PODC2019.VFTSpannersOptimal.FTGreedy
import Mathlib.Data.Nat.Choose.Cast

/-!
# The literal reading of Algorithm 1 is wrong

Algorithm 1 of Bodwin–Patel tests "is there a set `F` of `|F| ≤ f` vertices such that
`dist_{H \ F}(u, v) > k · w(u, v)`", without saying that `u, v ∉ F`. Read literally, `F = {u}` always
works (after deleting `u` there is no `u`–`v` path, distance `∞`), so for `f ≥ 1` every edge is added
and the output is `G` itself (`ftGreedyLiteral_eq`). On complete graphs this violates Corollary 2
(`literal_violates_corollary2`): with `f = 1` and stretch `3` the output has `n(n-1)/2` edges, which is
not `O(n^{3/2})`. The intended test (used in `FTGreedy.lean` and in the proof of Lemma 3) requires
`u, v ∉ F`. Definition 2 constrains `s, t ∉ F` implicitly, via Definition 1's `s, t ∈ V` applied to
`G \ F`. The counterexample uses the convention that the distance to a deleted vertex is `∞`.
-/

open Finset SimpleGraph FaultTolerantSpanners
open scoped ENNReal NNReal

namespace VFTSpannersOptimal

variable {V : Type*}

open Classical in
/-- The test of Algorithm 1 read literally: `F` may contain `u` or `v`. -/
noncomputable def vftTestLiteral (w : Sym2 V → ℝ≥0) (k f : ℕ) (H : SimpleGraph V) (u v : V) :
    Bool :=
  decide (∃ F : Finset V, #F ≤ f ∧ (k : ℝ≥0∞) * w s(u, v) < (H.deleteVerts F).wdist w u v)

/-- Algorithm 1 read literally. -/
noncomputable def ftGreedyLiteral (w : Sym2 V → ℝ≥0) (k f : ℕ) (L : List (V × V)) :
    SimpleGraph V :=
  greedy (vftTestLiteral w k f) L

/-- Deleting `u` disconnects `u` from every other vertex. -/
lemma wdist_deleteVerts_self_eq_top [DecidableEq V] {H : SimpleGraph V} {w : Sym2 V → ℝ≥0}
    {u v : V} (huv : u ≠ v) : (H.deleteVerts ({u} : Finset V)).wdist w u v = ⊤ := by
  have : IsEmpty ((H.deleteVerts ({u} : Finset V)).Walk u v) := by
    constructor
    intro p
    cases p with
    | nil => exact huv rfl
    | cons h _ => exact h.2.1 (by simp)
  exact iInf_of_empty _

lemma vftTestLiteral_eq_true [DecidableEq V] {w : Sym2 V → ℝ≥0} {k f : ℕ} (hf : 1 ≤ f)
    {H : SimpleGraph V} {u v : V} (huv : u ≠ v) : vftTestLiteral w k f H u v = true := by
  simp only [vftTestLiteral, decide_eq_true_eq]
  refine ⟨{u}, by simpa using hf, ?_⟩
  rw [wdist_deleteVerts_self_eq_top huv]
  exact ENNReal.mul_lt_top (by simp) (by simp)

lemma greedyList_eq_of_forall {dec : SimpleGraph V → V → V → Bool} :
    ∀ (l A : List (V × V)), (∀ B, ∀ e ∈ l, dec B e.1 e.2 = true) →
      l.foldl (greedyStep dec) A = A ++ l
  | [], A, _ => by simp
  | e :: l, A, h => by
    rw [List.foldl_cons]
    have hs : greedyStep dec A e = A ++ [e] := by simp [greedyStep, h _ e (by simp)]
    rw [hs, greedyList_eq_of_forall l _ (fun B e' he' => h B e' (by simp [he']))]
    simp

/-- **The literal Algorithm 1 adds every edge** (for `f ≥ 1`): its output is `edgeGraph L`, i.e. `G`
itself when `L` lists the edges of `G`. -/
theorem ftGreedyLiteral_eq [DecidableEq V] {w : Sym2 V → ℝ≥0} {k f : ℕ} (hf : 1 ≤ f)
    {L : List (V × V)} (hL : ∀ p ∈ L, p.1 ≠ p.2) :
    ftGreedyLiteral w k f L = edgeGraph L := by
  rw [ftGreedyLiteral, greedy, greedyList,
    greedyList_eq_of_forall L [] (fun B e he => vftTestLiteral_eq_true hf (hL e he))]
  rfl

/-- The list of all ordered pairs of distinct vertices of `Fin n`. -/
noncomputable def completeList (n : ℕ) : List (Fin n × Fin n) :=
  ((univ : Finset (Fin n × Fin n)).filter fun p => p.1 ≠ p.2).toList

lemma edgeGraph_completeList (n : ℕ) : edgeGraph (completeList n) = ⊤ := by
  ext u v
  simp only [edgeGraph_adj, completeList, mem_toList, mem_filter, mem_univ, true_and, top_adj]
  exact ⟨fun h => h.1, fun h => ⟨h, (u, v), h, rfl⟩⟩

/-- **Counterexample to the literal Algorithm 1.** With `f = 1`, unit weights and stretch `3`
(`k = 2` in Corollary 2), the literal algorithm on the complete graph `K_n` keeps all `n(n-1)/2`
edges, so no bound `C · n^{1+1/2} f^{1-1/2}` can hold. -/
theorem literal_violates_corollary2 (C : ℝ) :
    ∃ n : ℕ, C * (n : ℝ) ^ (1 + 1 / (2 : ℝ)) <
      ((ftGreedyLiteral (fun _ => (1 : ℝ≥0)) 3 1 (completeList n)).edgeSet.ncard : ℝ) := by
  classical
  set m : ℕ := ⌈2 * |C|⌉₊ + 2 with hm
  refine ⟨m ^ 2, ?_⟩
  rw [ftGreedyLiteral_eq le_rfl (by simp [completeList]), edgeGraph_completeList,
    ← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin, Nat.cast_choose_two]
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hpow : ((m ^ 2 : ℕ) : ℝ) ^ (1 + 1 / (2 : ℝ)) = (m : ℝ) ^ 3 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_mul hm0]
    norm_num
  rw [hpow]
  have hC : 2 * C ≤ (m : ℝ) - 2 := by
    have h1 : 2 * |C| ≤ (⌈2 * |C|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : C ≤ |C| := le_abs_self C
    simp only [hm, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hm2 : (2 : ℝ) ≤ m := by
    have : (0 : ℝ) ≤ (⌈2 * |C|⌉₊ : ℝ) := Nat.cast_nonneg _
    simp only [hm, Nat.cast_add, Nat.cast_ofNat]; linarith
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 3)]

end VFTSpannersOptimal
