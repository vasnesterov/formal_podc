import Mathlib.Data.List.SplitBy
import Mathlib.Logic.Relation

/-!
# Comparator-based γ-Batch-Order-Fairness (§4.2–4.3 of the FEAT paper)

Dinh, Kang, Sadoghi. *FEAT: Fair and Efficient Adversarial Transaction Ordering.* PODC 2026.

A *comparator* is a Boolean function `c : α → α → Bool`; `c a b = true` means "fairness requires
`a` before `b`". It is a *tournament* on a set `T` if for distinct `a, b ∈ T` exactly one of
`c a b`, `c b a` is `true` (we only need "at least one", `Total`).

A final ordering is a list `FO`; the transaction set is the set of its elements. Batches are the
strongly connected components of the comparator graph restricted to the elements of `FO`.

* `AdjConsistent c FO` — Definition 4.3 (Adjacent-Comparator Consistency).
* `GammaInduced c G FO` — Definition 4.2, for an abstract "γ-fraction of honest replicas receive
  `a` before `b`" relation `G` (instantiated concretely in `FEAT.lean`).
* `BatchOrderFair c G FO` — Definition 4.1 (comparator-based γ-Batch-Order-Fairness).
* `theorem_4_4` — Theorem 4.4: ACC + γ-induced ⇒ comparator-based γ-Batch-Order-Fairness.
-/

namespace Podc.FEATOrdering

open scoped List

variable {α : Type*}

/-- **Definition 4.3 (Adjacent-Comparator Consistency).** Every pair of adjacent transactions of
`FO` is ordered as the comparator requires. -/
def AdjConsistent (c : α → α → Bool) (FO : List α) : Prop :=
  FO.IsChain (fun a b => c a b = true)

/-- The comparator is a tournament on the elements of `FO`: for distinct `a, b`, at least one of
`c a b`, `c b a` holds (the paper also requires at most one, which we never need). -/
def Total (c : α → α → Bool) (FO : List α) : Prop :=
  ∀ a ∈ FO, ∀ b ∈ FO, a ≠ b → c a b = true ∨ c b a = true

/-- The edge `a → b` (`cmp(a, b) = True`) of the comparator graph on the transactions of `T`. -/
def Edge (c : α → α → Bool) (T : List α) (a b : α) : Prop := a ∈ T ∧ b ∈ T ∧ c a b = true

/-- `a ⇝ b`: reachability in the comparator graph on `T` (paths of length `≥ 0`). -/
def Reach (c : α → α → Bool) (T : List α) : α → α → Prop := Relation.ReflTransGen (Edge c T)

/-- `a ∼ b`: `a` and `b` lie in the same batch (strongly connected component). -/
def SameBatch (c : α → α → Bool) (T : List α) (a b : α) : Prop := Reach c T a b ∧ Reach c T b a

/-- **Definition 4.2 (γ-induced comparator).** `G a b` stands for "at least a `γ`-fraction of
honest replicas receive `a` before `b`". -/
def GammaInduced (c : α → α → Bool) (G : α → α → Prop) (FO : List α) : Prop :=
  ∀ a ∈ FO, ∀ b ∈ FO, G a b → c a b = true

/-- **Definition 4.1 (comparator-based γ-Batch-Order-Fairness).** `FO` is the concatenation of
non-empty contiguous blocks `B₁, …, B_k`, each of which is exactly a batch (an `∼`-class of the
transactions of `FO`), such that
1. (*linear batch partition*) for `i < j`, `T ∈ Bᵢ`, `T' ∈ Bⱼ`: `cmp(T, T') = True`;
2. (*γ-precedence respect*) if `G T T'` then `batch(T) ≤ batch(T')`, i.e. never `T ∈ Bⱼ`,
   `T' ∈ Bᵢ` with `i < j`. -/
def BatchOrderFair (c : α → α → Bool) (G : α → α → Prop) (FO : List α) : Prop :=
  ∃ B : List (List α), B.flatten = FO ∧ (∀ b ∈ B, b ≠ []) ∧
    (∀ b ∈ B, ∀ x ∈ b, ∀ y, y ∈ b ↔ SameBatch c FO x y) ∧
    B.Pairwise (fun b b' => ∀ x ∈ b, ∀ y ∈ b', c x y = true) ∧
    B.Pairwise (fun b b' => ∀ x ∈ b, ∀ y ∈ b', ¬ G y x)

/-! ### Auxiliary lemmas -/

section Aux

theorem sameBatch_refl (c : α → α → Bool) (T : List α) (a : α) : SameBatch c T a a :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem SameBatch.symm {c : α → α → Bool} {T : List α} {a b : α} (h : SameBatch c T a b) :
    SameBatch c T b a := ⟨h.2, h.1⟩

theorem SameBatch.trans {c : α → α → Bool} {T : List α} {a b d : α} (h : SameBatch c T a b)
    (h' : SameBatch c T b d) : SameBatch c T a d := ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- A chain stays a chain when we additionally record membership in the list. -/
theorem isChain_mem {R : α → α → Prop} {l : List α} (S : Set α) (hS : ∀ x ∈ l, x ∈ S)
    (h : l.IsChain R) : l.IsChain (fun a b => a ∈ S ∧ b ∈ S ∧ R a b) := by
  induction l with
  | nil => exact .nil
  | cons a t ih =>
    cases t with
    | nil => exact .singleton _
    | cons b t =>
      rw [List.isChain_cons_cons] at h ⊢
      exact ⟨⟨hS a (by simp), hS b (by simp), h.1⟩,
        ih (fun x hx => hS x (List.mem_cons_of_mem _ hx)) h.2⟩

/-- In a chain, an earlier element reaches every later one. -/
theorem transGen_of_sublist {R : α → α → Prop} {l : List α} (h : l.IsChain R) {x y : α}
    (hxy : [x, y] <+ l) : Relation.TransGen R x y := by
  have h' : l.IsChain (Relation.TransGen R) := h.imp fun _ _ hab => .single hab
  have hp := List.IsChain.pairwise h'
  have := hp.sublist hxy
  simpa using this

/-- With Adjacent-Comparator Consistency, `FO[a] ⇝ FO[b]` for `a < b` (preliminary fact of the
proof of Theorem 4.4). -/
theorem reach_of_sublist {c : α → α → Bool} {FO : List α} (h : AdjConsistent c FO) {x y : α}
    (hxy : [x, y] <+ FO) : Reach c FO x y :=
  (transGen_of_sublist (isChain_mem {z | z ∈ FO} (fun _ hz => hz) h) hxy).to_reflTransGen

theorem mem_or_sublist_getLast {l : List α} (hl : l ≠ []) {x : α} (hx : x ∈ l) :
    x = l.getLast hl ∨ [x, l.getLast hl] <+ l := by
  have e := List.dropLast_append_getLast hl
  rw [← e] at hx
  rcases List.mem_append.1 hx with h | h
  · right
    conv_rhs => rw [← e]
    exact List.Sublist.append (List.singleton_sublist.2 h) (List.Sublist.refl _)
  · left; simpa using h

theorem mem_or_sublist_head {l : List α} (hl : l ≠ []) {y : α} (hy : y ∈ l) :
    y = l.head hl ∨ [l.head hl, y] <+ l := by
  match l, hl with
  | a :: t, _ =>
    rcases List.mem_cons.1 hy with h | h
    · left; simpa using h
    · right; exact List.Sublist.cons_cons _ (List.singleton_sublist.2 h)

/-- Elements of an earlier block precede elements of a later block in the concatenation. -/
theorem pairwise_sublist_flatten (B : List (List α)) :
    B.Pairwise (fun b b' => ∀ x ∈ b, ∀ y ∈ b', [x, y] <+ B.flatten) := by
  induction B with
  | nil => exact .nil
  | cons b B ih =>
    refine List.pairwise_cons.2 ⟨fun b' hb' x hx y hy => ?_, ih.imp fun h x hx y hy => ?_⟩
    · rw [List.flatten_cons]
      exact List.Sublist.append (List.singleton_sublist.2 hx)
        (List.singleton_sublist.2 (List.mem_flatten.2 ⟨b', hb', hy⟩))
    · rw [List.flatten_cons]
      exact (h x hx y hy).trans (List.sublist_append_right _ _)

end Aux

/-! ### Theorem 4.4 -/

section Thm44

open Classical in
/-- Contiguity of batches: under ACC, the maximal runs of mutually equivalent adjacent elements
are pairwise non-equivalent ("Batch contiguity" in the proof of Theorem 4.4). -/
theorem pairwise_not_sameBatch {c : α → α → Bool} {FO : List α} (B : List (List α))
    (hreach : ∀ x y, [x, y] <+ B.flatten → Reach c FO x y)
    (hne : ∀ b ∈ B, b ≠ [])
    (hcut : B.IsChain (fun a b => ∃ ha hb,
      decide (SameBatch c FO (a.getLast ha) (b.head hb)) = false)) :
    B.Pairwise (fun b b' => ∀ x ∈ b, ∀ y ∈ b', ¬ SameBatch c FO x y) := by
  induction B with
  | nil => exact .nil
  | cons b B ih =>
    refine List.pairwise_cons.2 ⟨?_, ih (fun x y h => hreach x y
      (h.trans (by rw [List.flatten_cons]; exact List.sublist_append_right _ _)))
      (fun b' hb' => hne b' (List.mem_cons_of_mem _ hb')) hcut.tail⟩
    intro b' hb' x hx y hy hxy
    match B, hb', hcut with
    | b₁ :: B', hb', hcut =>
      rw [List.isChain_cons_cons] at hcut
      obtain ⟨hb, hb₁, hcut⟩ := hcut.1
      simp only [decide_eq_false_iff_not] at hcut
      apply hcut
      set u := b.getLast hb
      set v := b₁.head hb₁
      have hflat : (b :: b₁ :: B').flatten = b ++ (b₁ ++ B'.flatten) := by simp
      have hv : v ∈ b₁ := List.head_mem hb₁
      have hu : u ∈ b := List.getLast_mem hb
      -- `u ⇝ v`
      have huv : Reach c FO u v := hreach u v (by
        rw [hflat]
        exact List.Sublist.append (List.singleton_sublist.2 hu)
          (List.singleton_sublist.2 (List.mem_append_left _ hv)))
      -- `v ⇝ y`
      have hy' : y ∈ b₁ ++ B'.flatten := by
        rcases List.mem_cons.1 hb' with rfl | h
        · exact List.mem_append_left _ hy
        · exact List.mem_append_right _ (List.mem_flatten.2 ⟨b', h, hy⟩)
      have hvy : Reach c FO v y := by
        have hne' : b₁ ++ B'.flatten ≠ [] := by simp [hb₁]
        have hh : (b₁ ++ B'.flatten).head hne' = v := by
          simp [v, List.head_append_of_ne_nil hb₁]
        rcases mem_or_sublist_head hne' hy' with h | h
        · rw [h, hh]; exact .refl
        · rw [hh] at h
          exact hreach v y (by rw [hflat]; exact h.trans (List.sublist_append_right _ _))
      -- `x ⇝ u`
      have hxu : Reach c FO x u := by
        rcases mem_or_sublist_getLast hb hx with h | h
        · rw [h]; exact .refl
        · exact hreach x u (by rw [hflat]; exact h.trans (List.sublist_append_left _ _))
      exact ⟨huv, hvy.trans (hxy.2.trans hxu)⟩

open Classical in
/-- **Theorem 4.4 (Sufficiency of Adjacent-Comparator Consistency).** If the comparator is a
tournament on the transactions of `FO` and is γ-induced, and `FO` satisfies Adjacent-Comparator
Consistency, then `FO` satisfies comparator-based γ-Batch-Order-Fairness. The batches are the
maximal runs of adjacent equivalent transactions (`List.splitBy`). -/
theorem theorem_4_4 {c : α → α → Bool} {G : α → α → Prop} {FO : List α}
    (htot : Total c FO) (hγ : GammaInduced c G FO) (hacc : AdjConsistent c FO) :
    BatchOrderFair c G FO := by
  set r : α → α → Bool := fun a b => decide (SameBatch c FO a b)
  set B := FO.splitBy r
  have hflat : B.flatten = FO := List.flatten_splitBy r FO
  have hne : ∀ b ∈ B, b ≠ [] := fun b hb => List.ne_nil_of_mem_splitBy hb
  have hreach : ∀ x y, [x, y] <+ B.flatten → Reach c FO x y := fun x y h =>
    reach_of_sublist hacc (hflat ▸ h)
  have hsep := pairwise_not_sameBatch (c := c) (FO := FO) B hreach hne
    (List.isChain_getLast_head_splitBy r FO)
  have hord := pairwise_sublist_flatten B
  rw [hflat] at hord
  have hmemFO : ∀ b ∈ B, ∀ x ∈ b, x ∈ FO := fun b hb x hx =>
    hflat ▸ List.mem_flatten.2 ⟨b, hb, hx⟩
  -- elements of a block are equivalent
  have hin : ∀ b ∈ B, ∀ x ∈ b, ∀ y ∈ b, SameBatch c FO x y := by
    intro b hb x hx y hy
    have hch : b.IsChain (fun x y => r x y = true) := List.isChain_of_mem_splitBy hb
    have hch' : b.IsChain (fun x y => SameBatch c FO x y) := hch.imp fun a b h => by
      simpa [r] using h
    have : Trans (SameBatch c FO) (SameBatch c FO) (SameBatch c FO) := ⟨SameBatch.trans⟩
    have hpw := hch'.pairwise
    have : Std.Symm (SameBatch c FO) := ⟨fun _ _ h => h.symm⟩
    by_cases hxy : x = y
    · subst hxy; exact sameBatch_refl _ _ _
    · exact hpw.forall hx hy hxy
  refine ⟨B, hflat, hne, ?_, ?_, ?_⟩
  · intro b hb x hx y
    constructor
    · exact hin b hb x hx y
    · intro hxy
      by_cases hyx : y = x
      · exact hyx ▸ hx
      -- `y` is in `FO`, hence in some block
      have hyFO : y ∈ FO := by
        rcases Relation.ReflTransGen.cases_tail hxy.1 with h | ⟨z, _, hz⟩
        · exact absurd h hyx
        · exact hz.2.1
      rw [← hflat] at hyFO
      obtain ⟨b', hb', hy⟩ := List.mem_flatten.1 hyFO
      by_cases hbb : b = b'
      · exact hbb ▸ hy
      · have : Std.Symm (fun b b' : List α => ∀ x ∈ b, ∀ y ∈ b', ¬ SameBatch c FO x y) :=
          ⟨fun b b' h y hy x hx hyx => h x hx y hy hyx.symm⟩
        exact absurd hxy (hsep.forall hb hb' hbb x hx y hy)
  · refine (hsep.and hord).imp_of_mem ?_
    intro b b' hb hb' ⟨hs, ho⟩ x hx y hy
    by_contra hc
    have hxy : x ≠ y := fun h => hs x hx y hy (h ▸ sameBatch_refl _ _ _)
    have hyx : c y x = true := by
      rcases htot x (hmemFO b hb x hx) y (hmemFO b' hb' y hy) hxy with h | h
      · exact absurd h hc
      · exact h
    exact hs x hx y hy ⟨reach_of_sublist hacc (ho x hx y hy),
      .single ⟨hmemFO b' hb' y hy, hmemFO b hb x hx, hyx⟩⟩
  · refine (hsep.and hord).imp_of_mem ?_
    intro b b' hb hb' ⟨hs, ho⟩ x hx y hy hG
    have hyx := hγ y (hmemFO b' hb' y hy) x (hmemFO b hb x hx) hG
    exact hs x hx y hy ⟨reach_of_sublist hacc (ho x hx y hy),
      .single ⟨hmemFO b' hb' y hy, hmemFO b hb x hx, hyx⟩⟩

end Thm44

end Podc.FEATOrdering
