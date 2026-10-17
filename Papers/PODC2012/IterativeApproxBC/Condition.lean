import Podc.ApproxConsensus.DigraphConditions
import Mathlib

/-!
# The graph condition of Vaidya–Tseng–Liang (PODC 2012) and its combinatorics

* `Arrow G f A B` — Definition 1, `A ⇒ B`: some node of `B` has at least `f + 1` in-neighbours
  in `A` (shared definition `Cslib.ApproxConsensus.Arrow`).
* `Condition G f` — the necessary and sufficient condition (statement of Theorem 1): for every
  partition `F, L, C, R` of the nodes with `|F| ≤ f`, `L, R ≠ ∅`: `C ∪ R ⇒ L` or `L ∪ C ⇒ R`
  (`Cslib.ApproxConsensus.IterativeCondition`; it implies condition BCS / 3-reach,
  `IterativeCondition.threeReach`).
* Corollaries 1–3: `Condition.corollary1`, `Condition.three_mul_lt_card` (`n > 3f`),
  `Condition.inDegree` (`|N_i⁻| ≥ 2f + 1` when `f > 0`).
* `inArrow` (Definition 2), `propStep` / `Propagates` (Definition 3), Lemma 1
  (`Condition.propagates_of_not_arrow`), Lemma 2 (`Condition.propagates_or`).
-/

open Finset Cslib.ApproxConsensus

namespace IterativeApproxBC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The condition of Theorem 1 of [VTL12]: for every partition `F, L, C, R` of `V` with
`|F| ≤ f` and `L, R` non-empty, `C ∪ R ⇒ L` or `L ∪ C ⇒ R` (`Arrow`, Definition 1). The
definitions are `Cslib.ApproxConsensus.IterativeCondition` and `Cslib.ApproxConsensus.Arrow`
(`Podc/ApproxConsensus/DigraphConditions.lean`). -/
abbrev Condition (G : Digraph V) (f : ℕ) : Prop := IterativeCondition G f

variable {G : Digraph V} {f : ℕ}

/-- The condition in "fault-free set" form: with `X = V \ F`, for disjoint non-empty `L, R ⊆ X`,
`X \ L ⇒ L` or `X \ R ⇒ R` (here `C = X \ (L ∪ R)`). -/
theorem Condition.sdiff (hG : Condition G f) {F L R : Finset V} (hF : #F ≤ f)
    (hL : L ⊆ univ \ F) (hR : R ⊆ univ \ F) (hLR : Disjoint L R) (hL0 : L.Nonempty)
    (hR0 : R.Nonempty) :
    Arrow G f ((univ \ F) \ L) L ∨ Arrow G f ((univ \ F) \ R) R := by
  set C := (univ \ F) \ (L ∪ R) with hC
  have hFL : Disjoint F L := disjoint_left.mpr fun x hx hxL => (mem_sdiff.mp (hL hxL)).2 hx
  have hFR : Disjoint F R := disjoint_left.mpr fun x hx hxR => (mem_sdiff.mp (hR hxR)).2 hx
  have h := hG F L C R hFL (disjoint_left.mpr fun x hx hxC => by simp [hC] at hxC; tauto)
    hFR (disjoint_left.mpr fun x hx hxC => by simp [hC] at hxC; tauto) hLR
    (disjoint_left.mpr fun x hxC hx => by simp [hC] at hxC; tauto)
    (by ext x; simp [hC]; tauto) hF hL0 hR0
  have e1 : C ∪ R = (univ \ F) \ L := by
    ext x; simp only [hC, mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (h | h)
      · tauto
      · exact ⟨(mem_sdiff.mp (hR h)).2, disjoint_right.mp hLR h⟩
    · tauto
  have e2 : L ∪ C = (univ \ F) \ R := by
    ext x; simp only [hC, mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact ⟨(mem_sdiff.mp (hL h)).2, disjoint_left.mp hLR h⟩
      · tauto
    · tauto
  rwa [e1, e2] at h

/-- Corollary 1 of [VTL12]: for every partition `F, L, R` with `|F| ≤ f`, `L, R ≠ ∅`:
`L ⇒ R` or `R ⇒ L`. -/
theorem Condition.corollary1 (hG : Condition G f) {F L R : Finset V} (hFL : Disjoint F L)
    (hFR : Disjoint F R) (hLR : Disjoint L R) (hU : F ∪ L ∪ R = univ) (hF : #F ≤ f)
    (hL : L.Nonempty) (hR : R.Nonempty) : Arrow G f L R ∨ Arrow G f R L := by
  have := hG F L ∅ R hFL (disjoint_empty_right _) hFR (disjoint_empty_right _) hLR
    (disjoint_empty_left _) (by simpa using hU) hF hL hR
  simp only [empty_union, union_empty] at this
  exact this.symm

/-- Corollary 2 of [VTL12]: if the condition holds and `n ≥ 2`, then `n > 3f`. -/
theorem Condition.three_mul_lt_card (hG : Condition G f) (hn : 2 ≤ Fintype.card V) :
    3 * f < Fintype.card V := by
  by_contra hcon
  push Not at hcon
  set n := Fintype.card V with hn'
  have hf : 1 ≤ f := by omega
  obtain ⟨L, -, hL⟩ := exists_subset_card_eq (s := (univ : Finset V)) (n := min f (n - 1))
    (by rw [card_univ]; omega)
  obtain ⟨R, hRs, hR⟩ := exists_subset_card_eq (s := univ \ L) (n := min f (n - #L))
    (by rw [card_sdiff_of_subset (subset_univ _), card_univ]; omega)
  have hLR : Disjoint L R := disjoint_left.mpr fun x hx hxR => (mem_sdiff.mp (hRs hxR)).2 hx
  set F := univ \ (L ∪ R)
  have hFc : #F ≤ f := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_union_of_disjoint hLR]; omega
  have := hG.corollary1 (F := F) (L := L) (R := R) (disjoint_sdiff_self_left.mono_right
      subset_union_left) (disjoint_sdiff_self_left.mono_right subset_union_right) hLR
      (by ext x; simp only [F, mem_union, mem_sdiff, mem_univ, true_and]; tauto) hFc (by rw [← card_pos]; omega) (by rw [← card_pos]; omega)
  rcases this with h | h
  · exact not_arrow_of_card_le (by omega) h
  · exact not_arrow_of_card_le (by omega) h

/-- Corollary 3 of [VTL12]: if the condition holds, `n ≥ 2` and `f > 0`, every node has at least
`2f + 1` in-neighbours. -/
theorem Condition.inDegree (hG : Condition G f) (hn : 2 ≤ Fintype.card V) (hf : 0 < f)
    (i : V) : 2 * f + 1 ≤ #(inNbrs G i) := by
  by_contra hcon
  push Not at hcon
  have h3 := hG.three_mul_lt_card hn
  set N := inNbrs G i
  obtain ⟨F, hFN, hF⟩ := exists_subset_card_eq (s := N) (n := (#N + 1) / 2) (by omega)
  have hiN : i ∉ N := self_notMem_inNbrs G i
  have hiF : i ∉ F := fun h => hiN (hFN h)
  set R := univ \ (F ∪ {i})
  have hR : #R = Fintype.card V - #F - 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_union_of_disjoint
      (disjoint_singleton_right.mpr hiF), card_singleton]; omega
  have := hG.corollary1 (F := F) (L := {i}) (R := R) (disjoint_singleton_right.mpr hiF)
    (disjoint_sdiff_self_right.mono_left subset_union_left)
    (disjoint_singleton_left.mpr (by simp [R]))
    (by ext x; simp only [R, mem_union, mem_sdiff, mem_univ, true_and, mem_singleton]; tauto) (by omega) (singleton_nonempty i) (by rw [← card_pos]; omega)
  rcases this with h | h
  · exact not_arrow_of_card_le (by simp; omega) h
  · obtain ⟨v, hv, hc⟩ := h
    rw [mem_singleton] at hv; rw [hv] at hc
    change f + 1 ≤ #(N ∩ R) at hc
    have hsub : N ∩ R ⊆ N \ F := fun x hx => by
      simp only [mem_inter, R, mem_sdiff, mem_univ, mem_union, true_and] at hx
      exact mem_sdiff.mpr ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
    have := card_le_card hsub
    rw [card_sdiff_of_subset hFN] at this
    omega

/-- Under the condition (and `n ≥ 2`), every node has at least `2f` in-neighbours, so that
Algorithm 1 is well defined. -/
theorem Condition.two_mul_le_inDegree (hG : Condition G f) (hn : 2 ≤ Fintype.card V) (i : V) :
    2 * f ≤ #(inNbrs G i) := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp
  · have := hG.inDegree hn hf i; omega

/-! ## Propagation (Definitions 2, 3; Lemmas 1, 2) -/

/-- Definition 2 of [VTL12]: `in(A ⇒ B)`, the nodes of `B` with at least `f + 1` in-neighbours
in `A`. -/
noncomputable def inArrow (G : Digraph V) (f : ℕ) (A B : Finset V) : Finset V := by
  classical exact B.filter (fun v => f + 1 ≤ #(inNbrs G v ∩ A))

theorem mem_inArrow {A B : Finset V} {v : V} :
    v ∈ inArrow G f A B ↔ v ∈ B ∧ f + 1 ≤ #(inNbrs G v ∩ A) := by
  classical simp [inArrow]

theorem arrow_iff_inArrow_nonempty {A B : Finset V} : Arrow G f A B ↔ (inArrow G f A B).Nonempty := by
  simp [Arrow, Finset.Nonempty, mem_inArrow]

/-- One step of a propagating sequence inside `X`: `S ↦ S ∪ in(S ⇒ X \ S)` (Definition 3:
`A_{τ+1} = A_τ ∪ in(A_τ ⇒ B_τ)`, `B_{τ+1} = X \ A_{τ+1}`). -/
noncomputable def propStep (G : Digraph V) (f : ℕ) (X S : Finset V) : Finset V :=
  S ∪ inArrow G f S (X \ S)

/-- Definition 3 of [VTL12]: `A` propagates to `B` if iterating `propStep` from `A` inside
`A ∪ B` reaches `A ∪ B`. (The paper additionally requires `A_τ ⇒ B_τ` before the end, which holds
automatically for the first time `l` at which `B_l = ∅`.) -/
def Propagates (G : Digraph V) (f : ℕ) (A B : Finset V) : Prop :=
  ∃ l, (propStep G f (A ∪ B))^[l] A = A ∪ B

theorem subset_propStep (X S : Finset V) : S ⊆ propStep G f X S := subset_union_left

theorem propStep_subset {X S : Finset V} (h : S ⊆ X) : propStep G f X S ⊆ X :=
  union_subset h fun _ hv => (mem_sdiff.mp (mem_inArrow.mp hv).1).1

theorem propStep_mono (X : Finset V) : Monotone (propStep G f X) := by
  intro S S' h v hv
  rcases mem_union.mp hv with hv | hv
  · exact mem_union_left _ (h hv)
  · obtain ⟨hvX, hc⟩ := mem_inArrow.mp hv
    by_cases hvS' : v ∈ S'
    · exact mem_union_left _ hvS'
    · exact mem_union_right _ (mem_inArrow.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hvX).1, hvS'⟩,
        hc.trans (card_le_card (inter_subset_inter_left h))⟩)

theorem propStep_iter_subset {X S : Finset V} (h : S ⊆ X) (k : ℕ) :
    (propStep G f X)^[k] S ⊆ X := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact propStep_subset ih

theorem subset_propStep_iter (X S : Finset V) (k : ℕ) : S ⊆ (propStep G f X)^[k] S := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (subset_propStep _ _)

theorem propStep_iter_mono_right (X S : Finset V) {k k' : ℕ} (h : k ≤ k') :
    (propStep G f X)^[k] S ⊆ (propStep G f X)^[k'] S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact subset_propStep_iter _ _ _

/-- Once a fixpoint is reached, the iteration is constant. -/
theorem propStep_iter_stable {X S : Finset V} {k : ℕ}
    (h : (propStep G f X)^[k + 1] S = (propStep G f X)^[k] S) :
    ∀ j ≥ k, (propStep G f X)^[j] S = (propStep G f X)^[k] S := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [Function.iterate_succ_apply', ih,
      ← Function.iterate_succ_apply' (propStep G f X) k S, h]

/-- After `#X` steps the iteration from `S ⊆ X` has reached its fixpoint (the closure). -/
theorem propStep_iter_card_fix {X S : Finset V} (h : S ⊆ X) :
    propStep G f X ((propStep G f X)^[#X] S) = (propStep G f X)^[#X] S := by
  set g := propStep G f X
  have grow : ∀ k, (∀ j < k, g^[j + 1] S ≠ g^[j] S) → k ≤ #(g^[k] S) := by
    intro k
    induction k with
    | zero => intro; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih fun j hj => hk j (by omega)
      have hss : g^[k] S ⊂ g^[k + 1] S := by
        refine ssubset_of_subset_of_ne ?_ (hk k (by omega)).symm
        rw [Function.iterate_succ_apply']; exact subset_propStep _ _
      have := card_lt_card hss
      omega
  by_contra hne
  rw [show g (g^[#X] S) = g^[#X + 1] S from (Function.iterate_succ_apply' g #X S).symm] at hne
  have hall : ∀ j < #X + 1, g^[j + 1] S ≠ g^[j] S := by
    intro j hj hfix
    exact hne ((propStep_iter_stable hfix (#X + 1) (by omega)).trans
      (propStep_iter_stable hfix #X (by omega)).symm)
  have h1 := grow (#X + 1) hall
  have h2 : #(g^[#X + 1] S) ≤ #X := card_le_card (propStep_iter_subset h (#X + 1))
  omega

/-- The closure is closed: nothing outside it receives `f + 1` values from it. -/
theorem not_arrow_iter_card {X S : Finset V} (h : S ⊆ X) :
    ¬ Arrow G f ((propStep G f X)^[#X] S) (X \ (propStep G f X)^[#X] S) := by
  rw [arrow_iff_inArrow_nonempty]
  rintro ⟨v, hv⟩
  have hfix := propStep_iter_card_fix (G := G) (f := f) h
  have : v ∈ propStep G f X ((propStep G f X)^[#X] S) := mem_union_right _ hv
  rw [hfix] at this
  exact (mem_sdiff.mp (mem_inArrow.mp hv).1).2 this

theorem propagates_iff_iter_card {A B : Finset V} :
    Propagates G f A B ↔ (propStep G f (A ∪ B))^[#(A ∪ B)] A = A ∪ B := by
  constructor
  · rintro ⟨l, hl⟩
    apply subset_antisymm (propStep_iter_subset subset_union_left _)
    by_cases hlk : l ≤ #(A ∪ B)
    · exact hl.symm.subset.trans (propStep_iter_mono_right _ _ hlk)
    · have hfix := propStep_iter_card_fix (G := G) (f := f) (X := A ∪ B) (S := A) subset_union_left
      rw [← Function.iterate_succ_apply' (propStep G f (A ∪ B))] at hfix
      exact (hl.symm.trans (propStep_iter_stable hfix l (by omega))).subset
  · intro h; exact ⟨_, h⟩

/-- Lemma 1 of [VTL12]: if `A, B, F` partition `V` (`A, B ≠ ∅`, `|F| ≤ f`) and `B ⇏ A`, then
`A` propagates to `B`. -/
theorem Condition.propagates_of_not_arrow (hG : Condition G f) {F A B : Finset V} (hF : #F ≤ f)
    (hFA : Disjoint F A) (hFB : Disjoint F B) (hAB : Disjoint A B) (hU : F ∪ A ∪ B = univ)
    (hA : A.Nonempty) (hBA : ¬ Arrow G f B A) : Propagates G f A B := by
  have hX : A ∪ B = univ \ F := by
    ext x; simp only [mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact disjoint_right.mp hFA h
      · exact disjoint_right.mp hFB h
    · intro hx
      have : x ∈ F ∪ A ∪ B := hU ▸ mem_univ x
      simp only [mem_union] at this; tauto
  rw [propagates_iff_iter_card]
  set X := A ∪ B
  set cl := (propStep G f X)^[#X] A
  have hclX : cl ⊆ X := propStep_iter_subset subset_union_left _
  by_contra hne
  have hR : (X \ cl).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; exact hne (subset_antisymm hclX (sdiff_eq_empty_iff_subset.mp h))
  have hAcl : A ⊆ cl := subset_propStep_iter _ _ _
  rcases hG.sdiff (F := F) (L := A) (R := X \ cl) hF (hX ▸ subset_union_left)
    (hX ▸ sdiff_subset) (disjoint_sdiff.mono_left hAcl) hA hR with h | h
  · apply hBA
    rw [← hX] at h
    have : X \ A = B := by
      ext x; simp only [X, mem_sdiff, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro h; exact ⟨Or.inr h, disjoint_right.mp hAB h⟩
    rwa [this] at h
  · rw [← hX, Finset.sdiff_sdiff_eq_self hclX] at h
    exact not_arrow_iter_card subset_union_left h

/-- Lemma 2 of [VTL12]: if `A, B, F` partition `V` (`A, B ≠ ∅`, `|F| ≤ f`), then `A` propagates
to `B` or `B` propagates to `A`. (Proof via closures instead of the paper's Appendix B; the
hypotheses `A ∩ B = ∅`, `A, B ≠ ∅` of the paper turn out to be unnecessary.) -/
theorem Condition.propagates_or (hG : Condition G f) {F A B : Finset V} (hF : #F ≤ f)
    (hFA : Disjoint F A) (hFB : Disjoint F B) (hU : F ∪ A ∪ B = univ) :
    Propagates G f A B ∨ Propagates G f B A := by
  have hX : A ∪ B = univ \ F := by
    ext x; simp only [mem_union, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact disjoint_right.mp hFA h
      · exact disjoint_right.mp hFB h
    · intro hx
      have : x ∈ F ∪ A ∪ B := hU ▸ mem_univ x
      simp only [mem_union] at this; tauto
  set X := A ∪ B
  rw [propagates_iff_iter_card, propagates_iff_iter_card, union_comm B A]
  by_contra hcon
  push Not at hcon
  obtain ⟨hA', hB'⟩ := hcon
  set clA := (propStep G f X)^[#X] A
  have hclA : clA ⊆ X := propStep_iter_subset subset_union_left _
  set R := X \ clA
  have hR0 : R.Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; exact hA' (subset_antisymm hclA (sdiff_eq_empty_iff_subset.mp h))
  have hRB : R ⊆ B := by
    intro x hx
    obtain ⟨hxX, hxcl⟩ := mem_sdiff.mp hx
    rcases mem_union.mp hxX with h | h
    · exact absurd (subset_propStep_iter _ _ _ h) hxcl
    · exact h
  set clR := (propStep G f X)^[#X] R
  have hclR : clR ⊆ X := propStep_iter_subset sdiff_subset _
  have hclRB : clR ⊆ (propStep G f X)^[#X] B :=
    ((propStep_mono X).iterate _) hRB
  have hL0 : (X \ clR).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h
    exact hB' (subset_antisymm (propStep_iter_subset subset_union_right _)
      ((sdiff_eq_empty_iff_subset.mp h).trans hclRB))
  have hRclR : R ⊆ clR := subset_propStep_iter _ _ _
  rcases hG.sdiff (F := F) (L := X \ clR) (R := R) hF (hX ▸ sdiff_subset) (hX ▸ sdiff_subset)
    (disjoint_left.mpr fun x hx hxR => (mem_sdiff.mp hx).2 (hRclR hxR)) hL0 hR0 with h | h
  · rw [← hX, Finset.sdiff_sdiff_eq_self hclR] at h
    exact not_arrow_iter_card sdiff_subset h
  · rw [← hX, Finset.sdiff_sdiff_eq_self hclA] at h
    exact not_arrow_iter_card subset_union_left h

end IterativeApproxBC
