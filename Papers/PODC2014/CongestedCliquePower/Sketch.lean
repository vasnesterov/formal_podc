import Papers.PODC2014.CongestedCliquePower.Claim6

-- CSLib candidate (graph reconstruction from linear sketches, Becker et al. IPDPS 2011 style)

/-!
# Reconstructing degenerate graphs from linear sketches

The upper bound of Theorem 7 (Drucker–Kuhn–Oshman, PODC 2014) uses the one-round algorithm of
Becker, Matamala, Nisse, Rapaport, Suchan, Todinca (IPDPS 2011, the paper's reference [2]): every
node broadcasts `O(k log n)` bits, from which all nodes reconstruct the input graph if its
degeneracy is at most `k`. We formalize a version of this algorithm with linear sketches over
`𝔽₂`:

* `exists_independent`: there is a matrix `M : V → 𝔽₂^m` with `m = 2k·⌈log₂(n+1)⌉ + 1` in which
  every nonempty set of at most `2k` columns has a nonzero sum (counting argument).
* `sketch_injOn`: then the sketch `σ(S) = ∑_{v ∈ S} M v` is injective on sets of size `≤ k`.
* `eq_of_sketch`: a `k`-degenerate graph `G₁` and any graph `G₂` with the same degrees and the same
  neighbourhood sketches are equal (peeling: a vertex of small degree has its neighbourhood
  determined by its sketch; remove it and update the sketches).
-/

namespace Podc.CongestedCliquePower

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

/-- The linear sketch of a set of vertices: the sum of the columns of `M`. -/
def sketch (M : V → Fin m → ZMod 2) (S : Finset V) : Fin m → ZMod 2 := ∑ v ∈ S, M v

/-- Every nonempty set of at most `2k` columns of `M` has a nonzero sum. -/
def Independent (M : V → Fin m → ZMod 2) (k : ℕ) : Prop :=
  ∀ T : Finset V, T.Nonempty → T.card ≤ 2 * k → ∑ v ∈ T, M v ≠ 0

lemma add_self_vec (x : Fin m → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  fin_cases a <;> decide

omit [Fintype V] in
/-- The sketch is injective on sets of size at most `k`. -/
theorem sketch_injOn {M : V → Fin m → ZMod 2} {k : ℕ} (hM : Independent M k) {S S' : Finset V}
    (hS : S.card ≤ k) (hS' : S'.card ≤ k) (h : sketch M S = sketch M S') : S = S' := by
  by_contra hne
  have hsum : ∑ v ∈ (S \ S') ∪ (S' \ S), M v = 0 := by
    rw [sum_union (disjoint_sdiff_sdiff)]
    have e1 := sum_sdiff (s₁ := S ∩ S') (s₂ := S) (f := M) inter_subset_left
    have e2 := sum_sdiff (s₁ := S ∩ S') (s₂ := S') (f := M) inter_subset_right
    rw [sdiff_inter_self_left] at e1
    rw [sdiff_inter_self_right] at e2
    unfold sketch at h
    have : ∑ v ∈ S \ S', M v + ∑ v ∈ S' \ S, M v + (∑ v ∈ S ∩ S', M v + ∑ v ∈ S ∩ S', M v) =
        ∑ v ∈ S, M v + ∑ v ∈ S', M v := by rw [← e1, ← e2]; abel
    rw [add_self_vec, add_zero, h, add_self_vec] at this
    exact this
  refine hM _ ?_ ?_ hsum
  · by_contra hem
    rw [not_nonempty_iff_eq_empty, union_eq_empty, sdiff_eq_empty_iff_subset,
      sdiff_eq_empty_iff_subset] at hem
    exact hne (Subset.antisymm hem.1 hem.2)
  · calc ((S \ S') ∪ (S' \ S)).card ≤ (S \ S').card + (S' \ S).card := card_union_le _ _
      _ ≤ S.card + S'.card := add_le_add (card_le_card sdiff_subset) (card_le_card sdiff_subset)
      _ ≤ 2 * k := by omega

omit [DecidableEq V] in
/-- Sets of size at most `2k` inject into `Fin (2k) → Option V`. -/
lemma card_small_le (k : ℕ) :
    (univ.filter fun T : Finset V => T.card ≤ 2 * k).card ≤ (Fintype.card V + 1) ^ (2 * k) := by
  classical
  let g : Finset V → Fin (2 * k) → Option V := fun T i =>
    if h : i.1 < T.card then some (T.equivFin.symm ⟨i.1, h⟩) else none
  have hmem : ∀ T : Finset V, T.card ≤ 2 * k → ∀ v, v ∈ T ↔ ∃ i, g T i = some v := by
    intro T hT v
    constructor
    · intro hv
      refine ⟨⟨(T.equivFin ⟨v, hv⟩).1, by omega⟩, ?_⟩
      simp [g]
    · rintro ⟨i, hi⟩
      simp only [g] at hi
      split_ifs at hi with h
      · simp only [Option.some.injEq] at hi
        rw [← hi]; exact (T.equivFin.symm _).2
  have hinj : Set.InjOn g (univ.filter fun T : Finset V => T.card ≤ 2 * k) := by
    intro T hT T' hT' he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hT hT'
    ext v
    rw [hmem T hT, hmem T' hT', he]
  calc _ ≤ (univ : Finset (Fin (2 * k) → Option V)).card :=
        card_le_card_of_injOn g (fun _ _ => mem_coe.2 (mem_univ _)) hinj
    _ = _ := by simp

/-- Matrices for which a given nonempty set `T` of columns sums to zero are few. -/
lemma card_sum_eq_zero_le (T : Finset V) (hT : T.Nonempty) :
    (univ.filter fun M : V → Fin m → ZMod 2 => ∑ v ∈ T, M v = 0).card ≤
      (2 ^ m) ^ (Fintype.card V - 1) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hT
  let r : (V → Fin m → ZMod 2) → ({v // v ≠ v₀} → Fin m → ZMod 2) := fun M v => M v.1
  have hinj : Set.InjOn r (univ.filter fun M : V → Fin m → ZMod 2 => ∑ v ∈ T, M v = 0) := by
    intro M hM M' hM' he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hM hM'
    have hrest : ∀ v, v ≠ v₀ → M v = M' v := fun v hv => congrFun he ⟨v, hv⟩
    funext v
    by_cases hv : v = v₀
    · subst hv
      rw [← add_sum_erase T M hv₀] at hM
      rw [← add_sum_erase T M' hv₀] at hM'
      have : ∑ x ∈ T.erase v, M x = ∑ x ∈ T.erase v, M' x :=
        sum_congr rfl fun x hx => hrest x (ne_of_mem_erase hx)
      rw [this] at hM
      have h1 := eq_neg_of_add_eq_zero_left hM
      have h2 := eq_neg_of_add_eq_zero_left hM'
      rw [h1, h2]
    · exact hrest v hv
  calc _ ≤ (univ : Finset ({v // v ≠ v₀} → Fin m → ZMod 2)).card :=
        card_le_card_of_injOn r (fun _ _ => mem_coe.2 (mem_univ _)) hinj
    _ = (2 ^ m) ^ (Fintype.card V - 1) := by
        simp [Fintype.card_subtype_compl, ZMod.card]

/-- **Existence of the sketch matrix.** If `(n + 1)^(2k) < 2^m` (e.g. `m = 2k·⌈log₂(n+1)⌉ + 1`),
there is a matrix `M : V → 𝔽₂^m` all of whose nonempty sets of at most `2k` columns have nonzero
sums. -/
theorem exists_independent (k : ℕ) (hm : (Fintype.card V + 1) ^ (2 * k) < 2 ^ m) :
    ∃ M : V → Fin m → ZMod 2, Independent M k := by
  classical
  by_contra hno
  push Not at hno
  simp only [Independent, not_forall, not_not] at hno
  set n := Fintype.card V
  have hn : 0 < n := by
    obtain ⟨T, hT, -, -⟩ := hno 0
    exact Fintype.card_pos_iff.2 ⟨hT.choose⟩
  let Ts := univ.filter fun T : Finset V => T.Nonempty ∧ T.card ≤ 2 * k
  have hcover : (univ : Finset (V → Fin m → ZMod 2)) ⊆
      Ts.biUnion fun T => univ.filter fun M : V → Fin m → ZMod 2 => ∑ v ∈ T, M v = 0 := by
    intro M _
    obtain ⟨T, hT, hTk, hs⟩ := hno M
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, Ts]
    exact ⟨T, ⟨hT, hTk⟩, hs⟩
  have hcard := card_le_card hcover
  have h1 : (Ts.biUnion fun T => univ.filter fun M : V → Fin m → ZMod 2 =>
      ∑ v ∈ T, M v = 0).card ≤ Ts.card * (2 ^ m) ^ (n - 1) := by
    refine (card_biUnion_le).trans ?_
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun T hT => card_sum_eq_zero_le T (mem_filter.1 hT).2.1
  have h2 : Ts.card ≤ (n + 1) ^ (2 * k) :=
    (card_le_card fun T hT => by
      simp only [mem_filter, mem_univ, true_and, Ts] at hT ⊢; exact hT.2).trans (card_small_le k)
  have h3 : (univ : Finset (V → Fin m → ZMod 2)).card = (2 ^ m) ^ n := by simp [ZMod.card, n]
  rw [h3] at hcard
  have h4 : (2 ^ m) ^ n = 2 ^ m * (2 ^ m) ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h5 : (n + 1) ^ (2 * k) * (2 ^ m) ^ (n - 1) < 2 ^ m * (2 ^ m) ^ (n - 1) :=
    Nat.mul_lt_mul_of_pos_right hm (by positivity)
  have := hcard.trans (h1.trans (Nat.mul_le_mul_right _ h2))
  omega

omit [Fintype V] in
/-- The sketch of a set with one element removed. -/
lemma sketch_erase (M : V → Fin m → ZMod 2) (A : Finset V) (v : V) (hv : v ∈ A) :
    sketch M A = sketch M (A.erase v) + M v := by
  unfold sketch
  rw [← add_sum_erase A M hv, add_comm]

variable {k : ℕ}

omit [Fintype V] in
/-- Peeling step of the reconstruction, on a vertex set `U`. -/
theorem eq_on_of_sketch {M : V → Fin m → ZMod 2} (hM : Independent M k)
    (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₁ : IsDegenerate G₁ k) :
    ∀ U : Finset V, (∀ v ∈ U, (U.filter (G₁.Adj v)).card = (U.filter (G₂.Adj v)).card ∧
        sketch M (U.filter (G₁.Adj v)) = sketch M (U.filter (G₂.Adj v))) →
      ∀ v ∈ U, U.filter (G₁.Adj v) = U.filter (G₂.Adj v) := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hU
    rcases U.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨v, hv, hvk⟩ := h₁ U hne
    have hv_eq : U.filter (G₁.Adj v) = U.filter (G₂.Adj v) :=
      sketch_injOn hM hvk ((hU v hv).1 ▸ hvk) (hU v hv).2
    have hadj : ∀ w ∈ U, (G₁.Adj w v ↔ G₂.Adj w v) := by
      intro w hw
      have := congrArg (w ∈ ·) hv_eq
      simp only [mem_filter, hw, true_and, eq_iff_iff] at this
      rw [G₁.adj_comm, G₂.adj_comm]; exact this
    set U' := U.erase v
    have hlt : U' ⊂ U := erase_ssubset hv
    have hfe : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] w,
        U'.filter (G.Adj w) = (U.filter (G.Adj w)).erase v := fun G _ w => filter_erase _ _ _
    have hU' : ∀ w ∈ U', (U'.filter (G₁.Adj w)).card = (U'.filter (G₂.Adj w)).card ∧
        sketch M (U'.filter (G₁.Adj w)) = sketch M (U'.filter (G₂.Adj w)) := by
      intro w hw
      have hwU := mem_of_mem_erase hw
      obtain ⟨hc, hs⟩ := hU w hwU
      rw [hfe G₁, hfe G₂]
      by_cases ha : G₁.Adj w v
      · have hb : G₂.Adj w v := (hadj w hwU).1 ha
        have m1 : v ∈ U.filter (G₁.Adj w) := mem_filter.2 ⟨hv, ha⟩
        have m2 : v ∈ U.filter (G₂.Adj w) := mem_filter.2 ⟨hv, hb⟩
        refine ⟨by rw [card_erase_of_mem m1, card_erase_of_mem m2, hc], ?_⟩
        rw [sketch_erase M _ v m1, sketch_erase M _ v m2] at hs
        exact add_right_cancel hs
      · have hb : ¬ G₂.Adj w v := fun h => ha ((hadj w hwU).2 h)
        rw [erase_eq_of_notMem (fun h => ha (mem_filter.1 h).2),
          erase_eq_of_notMem (fun h => hb (mem_filter.1 h).2)]
        exact ⟨hc, hs⟩
    have ih' := ih U' hlt hU'
    intro w hw
    by_cases hwv : w = v
    · subst hwv; exact hv_eq
    have hw' : w ∈ U' := mem_erase.2 ⟨hwv, hw⟩
    have e := ih' w hw'
    rw [hfe G₁, hfe G₂] at e
    ext x
    by_cases hx : x = v
    · subst hx
      simp only [mem_filter, hv, true_and]
      exact hadj w hw
    · have := congrArg (x ∈ ·) e
      simpa [mem_erase, hx] using this

/-- **Reconstruction.** If `G₁` is `k`-degenerate and `G₂` has the same degrees and the same
neighbourhood sketches as `G₁` (for an `Independent` sketch matrix), then `G₁ = G₂`. -/
theorem eq_of_sketch {M : V → Fin m → ZMod 2} (hM : Independent M k)
    (G₁ G₂ : SimpleGraph V) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h₁ : IsDegenerate G₁ k)
    (hdeg : ∀ v, G₁.degree v = G₂.degree v)
    (hsk : ∀ v, sketch M (G₁.neighborFinset v) = sketch M (G₂.neighborFinset v)) : G₁ = G₂ := by
  have hn : ∀ (G : SimpleGraph V) [DecidableRel G.Adj] v,
      univ.filter (G.Adj v) = G.neighborFinset v := fun G _ v => by ext; simp
  have h := eq_on_of_sketch hM G₁ G₂ h₁ univ (fun v _ => by
    rw [hn G₁, hn G₂, SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
    exact ⟨hdeg v, hsk v⟩)
  ext v w
  have := congrArg (w ∈ ·) (h v (mem_univ v))
  simpa using this

end Podc.CongestedCliquePower
