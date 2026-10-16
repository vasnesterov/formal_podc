import Papers.PODC2021.AllYouNeedIsDAG.ChainQuality

/-!
# Chain quality fails for some deterministic orders

`order_vertices` delivers a causal history "in some deterministic order". If that order lists the
vertices by *source first* (then round), chain quality (Section 3) fails already in a failure-free
looking lock-step execution with `n = 4`, `f = 1` and Byzantine process `0` (which behaves
correctly): the leader `(1, 1)` of wave 1 is committed and delivered alone, then the leader
`(5, 1)` of wave 2 is committed and its causal history (all of rounds `1..4`) is delivered starting
with `(1, 0), (2, 0), (3, 0), (4, 0)`. The prefix of size `2f + 1 = 3` contains only one block of a
correct process (`f + 1 = 2` required).

With a round-major order the claim holds (`chain_quality`).
-/

namespace DagRider.ChainQualityCounterexample

open Finset

/-- Complete strong edges, no weak edges. -/
def C : Content (Fin 4) Unit := ⟨fun _ => univ, fun _ => ∅, fun _ => ()⟩

/-- The coin always elects process `1`. -/
def coin : ℕ → Fin 4 := fun _ => 1

/-- Rounds `1..4w`. -/
def D (w : ℕ) : Finset (Vtx (Fin 4)) := (Finset.Icc 1 (4 * w)) ×ˢ Finset.univ

/-- Deliver by source first, then by round. -/
def sortSrc (s : Finset (Vtx (Fin 4))) : List (Vtx (Fin 4)) :=
  (List.finRange 4).flatMap (fun k =>
    ((List.range (s.sup Prod.fst + 1)).filter (fun r => decide ((r, k) ∈ s))).map (fun r => (r, k)))

lemma sortSrc_spec : SortSpec sortSrc := by
  intro s
  refine ⟨?_, fun x => ?_⟩
  · rw [sortSrc, List.nodup_flatMap]
    refine ⟨fun k _ => ((List.nodup_range).filter _).map (fun a b h => by simpa using h), ?_⟩
    refine (List.nodup_finRange 4).pairwise_of_forall_ne (fun k _ k' _ hkk' => ?_)
    rw [Function.onFun, List.disjoint_left]
    intro y hy hy'
    simp only [List.mem_map] at hy hy'
    obtain ⟨_, _, rfl⟩ := hy
    obtain ⟨_, _, h⟩ := hy'
    exact hkk' (congrArg Prod.snd h).symm
  · simp only [sortSrc, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
      List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨k, r, ⟨-, hr⟩, rfl⟩; exact hr
    · intro hx
      exact ⟨x.2, x.1, ⟨Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) hx), hx⟩, rfl⟩

/-- Delivery of one leader, given its new causal history `E`. -/
lemma deliverOne_eq {P : Type*} {B : Type*} {C : Content P B}
    {sortV : Finset (Vtx P) → List (Vtx P)} {D : Finset (Vtx P)} {L : List (Vtx P)} {v : Vtx P}
    {E : Finset (Vtx P)} (h : ∀ x, x ∈ E ↔ x ∈ hist C D v ∧ x ∉ L) :
    deliverOne C sortV D L v = L ++ sortV E := by
  classical
  unfold deliverOne
  congr 2
  ext x
  rw [Finset.mem_filter, h]

lemma D_closed (w : ℕ) : Closed C (D w) := by
  intro v hv u ⟨he, hu⟩
  simp only [D, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hv ⊢
  rcases he with ⟨h, -⟩ | h
  · omega
  · simp [C] at h

lemma D_valid (w : ℕ) : Valid 1 C (D w) := by
  intro v _; simp [C]

lemma path_iff {v u : Vtx (Fin 4)} : Path C v u ↔ u = v ∨ (1 ≤ u.1 ∧ u.1 < v.1) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ e ih =>
      obtain ⟨he, h1⟩ := e
      rcases he with ⟨h, -⟩ | h
      · right; rcases ih with rfl | ih <;> omega
      · simp [C] at h
  · rintro (rfl | ⟨h1, h2⟩)
    · exact Relation.ReflTransGen.refl
    · obtain ⟨k, hk⟩ : ∃ k, v.1 = u.1 + k + 1 := ⟨v.1 - u.1 - 1, by omega⟩
      induction k generalizing v with
      | zero =>
        exact Relation.ReflTransGen.single ⟨Or.inl ⟨by omega, by simp [C]⟩, h1⟩
      | succ k ih =>
        have hmid : Path C (v.1 - 1, u.2) u := ih (by simp; omega) (by simp; omega)
        exact Relation.ReflTransGen.head ⟨Or.inl ⟨by simp; omega, by simp [C]⟩, by simp; omega⟩ hmid

lemma hist1 : hist C (D 1) (1, 1) = {(1, 1)} := by
  ext ⟨a, b⟩
  rw [mem_hist, path_iff, Finset.mem_singleton]
  simp only [D, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true, Prod.mk.injEq]
  omega

lemma hist2 : hist C (D 2) (5, 1) = insert (5, 1) ((Finset.Icc 1 4) ×ˢ univ) := by
  ext ⟨a, b⟩
  rw [mem_hist, path_iff, Finset.mem_insert]
  simp only [D, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true, Prod.mk.injEq]
  omega

lemma facts :
    leader coin (D 1) 1 = some (1, 1) ∧ commitCount C (D 1) (1, 1) 1 = 4 ∧
    leader coin (D 2) 2 = some (5, 1) ∧ commitCount C (D 2) (5, 1) 2 = 4 ∧
    chain C coin (D 2) (5, 1) (wavesDown 2 1) = [] := by
  decide +kernel

lemma sort2 : sortSrc ((Finset.Icc 1 4 ×ˢ univ).erase (1, 1) ∪ {(5, 1)}) =
    [(1, 0), (2, 0), (3, 0), (4, 0), (2, 1), (3, 1), (4, 1), (5, 1),
     (1, 2), (2, 2), (3, 2), (4, 2), (1, 3), (2, 3), (3, 3), (4, 3)] := by
  decide +kernel

lemma sort1 : sortSrc {(1, 1)} = [(1, 1)] := by decide +kernel

/-- **Chain quality fails for a source-major delivery order** (`n = 3f + 1 = 4`, Byzantine set
`{0}`): after two waves, the prefix of size `2f + 1 = 3` of the output contains two Byzantine
blocks, i.e. only one block of a correct process. -/
theorem chain_quality_false :
    SortSpec sortSrc ∧ (∀ w, Closed C (D w) ∧ Valid 1 C (D w)) ∧
    ((orun 1 C coin sortSrc D 2).delivered.take 3) = [(1, 1), (1, 0), (2, 0)] ∧
    (((orun 1 C coin sortSrc D 2).delivered.take (2 * 1 + 1)).filter
        (fun x => decide (x.2 ∈ ({0} : Finset (Fin 4))))).length = 2 := by
  obtain ⟨h1, h1c, h2, h2c, hch⟩ := facts
  have o1 : orun 1 C coin sortSrc D 1 = ⟨1, [(1, 1)]⟩ := by
    show waveReady 1 C coin sortSrc (D 1) 1 ⟨0, []⟩ = _
    simp only [waveReady, h1, h1c, show 2 * 1 + 1 ≤ 4 from by decide, ↓reduceIte]
    have hw : wavesDown 1 0 = [] := rfl
    simp only [hw, chain, List.reverse_cons, List.reverse_nil, List.nil_append, deliverAll,
      List.foldl_cons, List.foldl_nil]
    rw [deliverOne_eq (E := {(1, 1)}) (fun x => by rw [hist1]; simp), sort1]
    rfl
  have o2 : (orun 1 C coin sortSrc D 2).delivered =
      [(1, 1)] ++ [(1, 0), (2, 0), (3, 0), (4, 0), (2, 1), (3, 1), (4, 1), (5, 1),
     (1, 2), (2, 2), (3, 2), (4, 2), (1, 3), (2, 3), (3, 3), (4, 3)] := by
    show (waveReady 1 C coin sortSrc (D 2) 2 (orun 1 C coin sortSrc D 1)).delivered = _
    rw [o1]
    simp only [waveReady, h2, h2c, show 2 * 1 + 1 ≤ 4 from by decide, ↓reduceIte, hch,
      List.reverse_cons, List.reverse_nil, List.nil_append, deliverAll, List.foldl_cons,
      List.foldl_nil]
    rw [deliverOne_eq (E := (Finset.Icc 1 4 ×ˢ univ).erase (1, 1) ∪ {(5, 1)}) (fun x => by
      rw [hist2]; obtain ⟨a, b⟩ := x
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_univ, and_true, Finset.mem_singleton, Finset.mem_insert, List.mem_singleton,
        Prod.mk.injEq, ne_eq]
      constructor
      · rintro (⟨h, h1, h2⟩ | ⟨rfl, rfl⟩)
        · exact ⟨Or.inr ⟨h1, h2⟩, h⟩
        · exact ⟨Or.inl ⟨rfl, rfl⟩, by omega⟩
      · rintro ⟨⟨rfl, rfl⟩ | ⟨h1, h2⟩, h⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨h, h1, h2⟩), sort2]
  refine ⟨sortSrc_spec, fun w => ⟨D_closed w, D_valid w⟩, ?_, ?_⟩
  · rw [o2]; rfl
  · rw [o2]; decide

end DagRider.ChainQualityCounterexample
