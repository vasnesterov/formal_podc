import Mathlib
import Cslib.Computability.Distributed.Local.Locality

/-!
# Auxiliary lemmas for Theorem 5 (order-invariance)

* `IsLocalIso`: a map `f : V → W` that identifies a set `S ⊆ V` closed under adjacency with a union
  of connected components of `H`; it preserves distances (`IsLocalIso.edist_eq`) and nothing
  outside `f '' S` is reachable from `f '' S` (`IsLocalIso.exists_of_edist_ne_top`).
* `exists_closedBall_card_le`: balls of radius `t` in graphs of maximum degree `≤ Δ` have at most
  `(Δ + 1) ^ t` nodes.
* `enumF F i`: the `i`-th smallest element of a finite set `F ⊆ ℕ`.
-/

namespace Podc.LocalAdvice.OrderInvariance

open SimpleGraph

section Transfer

variable {V W : Type*}

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/
/-- `f` identifies the set `S` (closed under adjacency in `G`) with a union of connected
components of `H`. -/
structure IsLocalIso (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (S : Set V) : Prop where
  injOn : Set.InjOn f S
  closedG : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S
  closedH : ∀ a ∈ S, ∀ y, H.Adj (f a) y → ∃ b ∈ S, f b = y
  adj_iff : ∀ a ∈ S, ∀ b ∈ S, H.Adj (f a) (f b) ↔ G.Adj a b

variable {G : SimpleGraph V} {H : SimpleGraph W} {f : V → W} {S : Set V}

lemma IsLocalIso.lift (h : IsLocalIso G H f S) {w₁ w₂ : W} (p : H.Walk w₁ w₂) :
    ∀ a ∈ S, f a = w₁ → ∃ b ∈ S, f b = w₂ ∧ ∃ q : G.Walk a b, q.length = p.length := by
  induction p with
  | nil => intro a ha hfa; exact ⟨a, ha, hfa, Walk.nil, rfl⟩
  | cons hadj p ih =>
    intro a ha hfa
    subst hfa
    obtain ⟨b, hb, rfl⟩ := h.closedH a ha _ hadj
    obtain ⟨c, hc, hfc, q, hq⟩ := ih b hb rfl
    exact ⟨c, hc, hfc, Walk.cons ((h.adj_iff a ha b hb).1 hadj) q, by simp [hq]⟩

lemma IsLocalIso.push (h : IsLocalIso G H f S) {a b : V} (q : G.Walk a b) (ha : a ∈ S) :
    ∃ p : H.Walk (f a) (f b), p.length = q.length := by
  induction q with
  | nil => exact ⟨Walk.nil, rfl⟩
  | cons hadj q ih =>
    obtain ⟨p, hp⟩ := ih (h.closedG _ ha _ hadj)
    exact ⟨Walk.cons ((h.adj_iff _ ha _ (h.closedG _ ha _ hadj)).2 hadj) p, by simp [hp]⟩

lemma IsLocalIso.exists_of_edist_ne_top (h : IsLocalIso G H f S) {a : V} (ha : a ∈ S) {w : W}
    (hw : H.edist (f a) w ≠ ⊤) : ∃ b ∈ S, f b = w := by
  obtain ⟨p⟩ := edist_ne_top_iff_reachable.1 hw
  obtain ⟨b, hb, hfb, -⟩ := h.lift p a ha rfl
  exact ⟨b, hb, hfb⟩

lemma IsLocalIso.edist_eq (h : IsLocalIso G H f S) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    H.edist (f a) (f b) = G.edist a b := by
  apply le_antisymm
  · by_cases hr : G.Reachable a b
    · obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_edist
      obtain ⟨p, hp⟩ := h.push q ha
      rw [← hq, ← hp]; exact edist_le p
    · rw [edist_eq_top_of_not_reachable hr]; exact le_top
  · by_cases hr : H.Reachable (f a) (f b)
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
      obtain ⟨c, hc, hfc, q, hq⟩ := h.lift p a ha rfl
      have : c = b := h.injOn hc hb hfc
      subst this
      rw [← hp, ← hq]; exact edist_le q
    · rw [edist_eq_top_of_not_reachable hr]; exact le_top

/-- Graph maps along embeddings are local isomorphisms. -/
lemma isLocalIso_map (G : SimpleGraph V) (e : V ↪ W) :
    IsLocalIso G (G.map e) e Set.univ where
  injOn := e.injective.injOn
  closedG := fun _ _ _ _ => trivial
  closedH := by
    intro a _ y hy
    obtain ⟨_, b, -, -, rfl⟩ := (map_adj e G _ _).1 hy
    exact ⟨b, trivial, rfl⟩
  adj_iff := fun _ _ _ _ => map_adj_apply

end Transfer

section Ball

variable {V : Type*}

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Ball.lean
/-- Balls of radius `t` in a graph of maximum degree `≤ Δ` have at most `(Δ + 1) ^ t` nodes. -/
lemma exists_closedBall_card_le {G : SimpleGraph V} {Δ : ℕ} (hfin : ∀ v, (G.neighborSet v).Finite)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ Δ) (t : ℕ) (c : V) :
    ∃ F : Finset V, (F : Set V) = G.closedBall c t ∧ F.card ≤ (Δ + 1) ^ t := by
  classical
  induction t generalizing c with
  | zero => exact ⟨{c}, by simp, by simp⟩
  | succ t ih =>
    choose F hF hFc using ih
    set N := (hfin c).toFinset with hN
    refine ⟨F c ∪ N.biUnion F, ?_, ?_⟩
    · ext v
      simp only [Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Finset.mem_coe,
        Set.mem_iUnion, exists_prop, hN, Set.Finite.mem_toFinset, mem_neighborSet]
      rw [mem_closedBall_succ_iff]
      simp only [← hF, Finset.mem_coe]
    · have hNc : N.card ≤ Δ := by
        rw [hN, ← Set.ncard_eq_toFinset_card _ (hfin c)]; exact hdeg c
      calc (F c ∪ N.biUnion F).card ≤ (F c).card + (N.biUnion F).card := Finset.card_union_le _ _
        _ ≤ (Δ + 1) ^ t + N.card * (Δ + 1) ^ t := by
            gcongr
            · exact hFc c
            · calc (N.biUnion F).card ≤ ∑ a ∈ N, (F a).card := Finset.card_biUnion_le
                _ ≤ N.card • (Δ + 1) ^ t := Finset.sum_le_card_nsmul _ _ _ fun a _ => hFc a
                _ = N.card * (Δ + 1) ^ t := smul_eq_mul _ _
        _ ≤ (Δ + 1) ^ t + Δ * (Δ + 1) ^ t := by gcongr
        _ = (Δ + 1) ^ (t + 1) := by ring

end Ball

section Enum

/-- The `i`-th smallest element of `F` (`0` if `i ≥ |F|`). -/
noncomputable def enumF (F : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < F.card then F.orderEmbOfFin rfl ⟨i, h⟩ else 0

variable {F : Finset ℕ}

lemma enumF_of_lt {i : ℕ} (h : i < F.card) : enumF F i = F.orderEmbOfFin rfl ⟨i, h⟩ := by
  simp [enumF, h]

lemma enumF_mem {i : ℕ} (h : i < F.card) : enumF F i ∈ F := by
  rw [enumF_of_lt h]; exact Finset.orderEmbOfFin_mem _ _ _

lemma enumF_lt_iff {i j : ℕ} (hi : i < F.card) (hj : j < F.card) :
    enumF F i < enumF F j ↔ i < j := by
  rw [enumF_of_lt hi, enumF_of_lt hj, OrderEmbedding.lt_iff_lt, Fin.mk_lt_mk]

lemma enumF_inj {i j : ℕ} (hi : i < F.card) (hj : j < F.card) :
    enumF F i = enumF F j ↔ i = j := by
  rw [enumF_of_lt hi, enumF_of_lt hj, (F.orderEmbOfFin rfl).injective.eq_iff, Fin.mk.injEq]

lemma exists_enumF {v : ℕ} (hv : v ∈ F) : ∃ i < F.card, enumF F i = v := by
  have : v ∈ Set.range (F.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hv
  obtain ⟨⟨i, hi⟩, hiv⟩ := this
  exact ⟨i, hi, by rw [enumF_of_lt hi]; exact hiv⟩

/-- Characterisation of `enumF` by monotonicity. -/
lemma enumF_unique {g : ℕ → ℕ} (hg : ∀ i < F.card, g i ∈ F)
    (hmono : ∀ i j, i < j → j < F.card → g i < g j) : ∀ i < F.card, enumF F i = g i := by
  intro i hi
  have := Finset.orderEmbOfFin_unique (s := F) (f := fun i : Fin F.card => g i) rfl
    (fun x => hg x x.isLt) (fun x y hxy => hmono x y hxy y.isLt)
  rw [enumF_of_lt hi]
  exact (congrFun this ⟨i, hi⟩).symm

lemma enumF_map (e : ℕ ↪o ℕ) {i : ℕ} (hi : i < F.card) :
    enumF (F.map e.toEmbedding) i = e (enumF F i) := by
  have hc : (F.map e.toEmbedding).card = F.card := Finset.card_map _
  refine enumF_unique (g := fun i => e (enumF F i)) ?_ ?_ i (hc ▸ hi)
  · intro i hi; rw [hc] at hi
    exact Finset.mem_map_of_mem _ (enumF_mem hi)
  · intro i j hij hj; rw [hc] at hj
    exact e.strictMono ((enumF_lt_iff (hij.trans hj) hj).2 hij)

end Enum

section Struct

variable {L : Type*}

/-- A *structure*: an adjacency matrix, labels and a centre on `Fin s`. Its realization on an
`s`-element set `X ⊆ ℕ` is a labelled graph on `ℕ`. -/
abbrev Struct (s : ℕ) (L : Type*) := (Fin s → Fin s → Bool) × (Fin s → L) × Fin s

open Classical in
/-- The structure of a (localized) labelled graph `Lg, x` on the finite set `F` with centre `v`:
the elements of `F` in increasing order, followed by phantom positions. -/
noncomputable def mkStruct (s : ℕ) [NeZero s] (F : Finset ℕ) (Lg : SimpleGraph ℕ) (x : ℕ → L)
    (v : ℕ) : Struct s L :=
  (fun i j => decide (i.val < F.card ∧ j.val < F.card ∧ Lg.Adj (enumF F i) (enumF F j)),
   fun i => if i.val < F.card then x (enumF F i) else x v,
   Classical.epsilon (fun i : Fin s => i.val < F.card ∧ enumF F i = v))

/-- The graph of the structure `S` realized along `φ : Fin s → ℕ`. -/
def realGraph {s : ℕ} (S : Struct s L) (φ : Fin s → ℕ) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun a b => ∃ i j, φ i = a ∧ φ j = b ∧ S.1 i j = true

/-- The labels of the structure `S` realized along `φ : Fin s → ℕ`. -/
noncomputable def realLab {s : ℕ} (S : Struct s L) (φ : Fin s → ℕ) : ℕ → L :=
  Function.extend φ S.2.1 (fun _ => S.2.1 S.2.2)

/-- The structure is invariant under order embeddings. -/
lemma mkStruct_map (s : ℕ) [NeZero s] (e : ℕ ↪o ℕ) (F : Finset ℕ) {Lg Lg' : SimpleGraph ℕ}
    {x x' : ℕ → L} {v : ℕ} (hL : ∀ a ∈ F, ∀ b ∈ F, Lg'.Adj (e a) (e b) ↔ Lg.Adj a b)
    (hx : ∀ a ∈ F, x' (e a) = x a) (hv : x' (e v) = x v) :
    mkStruct s (F.map e.toEmbedding) Lg' x' (e v) = mkStruct s F Lg x v := by
  simp only [mkStruct, Finset.card_map]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i j
    simp only
    by_cases hi : i.val < F.card
    · by_cases hj : j.val < F.card
      · rw [enumF_map e hi, enumF_map e hj, hL _ (enumF_mem hi) _ (enumF_mem hj),
          Finset.card_map]
      · simp [hj]
    · simp [hi]
  · funext i
    simp only
    by_cases hi : i.val < F.card
    · simp only [hi, ite_true, enumF_map e hi, hx _ (enumF_mem hi)]
    · simp only [hi, ite_false, hv]
  · simp only
    congr 1
    funext i
    apply propext
    constructor
    · rintro ⟨hi, h⟩; exact ⟨hi, e.injective (by rw [← h, enumF_map e hi])⟩
    · rintro ⟨hi, h⟩; exact ⟨hi, by rw [enumF_map e hi, h]⟩

variable {s : ℕ} [NeZero s] {F : Finset ℕ} {Lg : SimpleGraph ℕ} {x : ℕ → L} {v : ℕ}
  {φ : Fin s → ℕ}

/-- Realizing the structure of `Lg` along a map that agrees with an embedding `E` on the real
positions gives back the image of `Lg` (if the edges of `Lg` lie in `F`). -/
lemma realGraph_mkStruct (hF : F.card ≤ s) (hLg : ∀ a b, Lg.Adj a b → a ∈ F) (E : ℕ ↪ ℕ)
    (hφ : ∀ i : Fin s, i.val < F.card → φ i = E (enumF F i)) :
    realGraph (mkStruct s F Lg x v) φ = Lg.map E := by
  ext a b
  simp only [realGraph, mkStruct, fromRel_adj, map_adj, decide_eq_true_eq]
  constructor
  · rintro ⟨-, ⟨i, j, rfl, rfl, hi, hj, h⟩ | ⟨i, j, rfl, rfl, hi, hj, h⟩⟩
    · exact ⟨_, _, h, (hφ i hi).symm, (hφ j hj).symm⟩
    · exact ⟨_, _, h.symm, (hφ j hj).symm, (hφ i hi).symm⟩
  · rintro ⟨u, w, h, rfl, rfl⟩
    refine ⟨fun h' => h.ne (E.injective h'), Or.inl ?_⟩
    obtain ⟨i, hi, rfl⟩ := exists_enumF (hLg _ _ h)
    obtain ⟨j, hj, rfl⟩ := exists_enumF (hLg _ _ h.symm)
    exact ⟨⟨i, hi.trans_le hF⟩, ⟨j, hj.trans_le hF⟩, hφ ⟨i, _⟩ hi, hφ ⟨j, _⟩ hj, hi, hj, h⟩

lemma realLab_mkStruct (hF : F.card ≤ s) (E : ℕ ↪ ℕ) (hφinj : Function.Injective φ)
    (hφ : ∀ i : Fin s, i.val < F.card → φ i = E (enumF F i)) {a : ℕ} (ha : a ∈ F) :
    realLab (mkStruct s F Lg x v) φ (E a) = x a := by
  obtain ⟨i, hi, rfl⟩ := exists_enumF ha
  rw [← hφ ⟨i, hi.trans_le hF⟩ hi, realLab, hφinj.extend_apply]
  simp [mkStruct, hi]

lemma centre_mkStruct (hF : F.card ≤ s) (E : ℕ ↪ ℕ)
    (hφ : ∀ i : Fin s, i.val < F.card → φ i = E (enumF F i)) (hv : v ∈ F) :
    φ (mkStruct s F Lg x v).2.2 = E v := by
  obtain ⟨i, hi, hiv⟩ := exists_enumF hv
  have := Classical.epsilon_spec (p := fun i : Fin s => i.val < F.card ∧ enumF F i = v)
    ⟨⟨i, hi.trans_le hF⟩, hi, hiv⟩
  simp only [mkStruct]
  rw [hφ _ this.1, this.2]

end Struct

end Podc.LocalAdvice.OrderInvariance
