import Mathlib

/-!
# Counting lemmas for Section 4 (Lemmas 4.1–4.5, pigeonhole parts)

* `card_filter_small_class_le`: at most `m · |β|` elements lie in classes (fibres of `f`) of size
  `≤ m` (the paper's "lonely nodes", with `m = 2` instead of `m = 1`, see `differencies.md`).
* `select13`: the parameter selection of the proof of Theorem 1.3 (Lemmas 4.1–4.3), for abstract
  "views" `fA`, `fB`, `fm`.
-/

namespace Podc.DynamicSubgraphFinding

open Finset

-- CSLib candidate: Cslib/Foundations/Combinatorics/Pigeonhole.lean
lemma card_filter_small_class_le {α β : Type} [DecidableEq β] [Fintype β] (S : Finset α)
    (f : α → β) (m : ℕ) :
    (S.filter (fun u => (S.filter (fun v => f v = f u)).card ≤ m)).card ≤ m * Fintype.card β := by
  classical
  set F := S.filter (fun u => (S.filter (fun v => f v = f u)).card ≤ m)
  rw [card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [mul_comm, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ (fun y _ => ?_)
  by_cases hne : (F.filter (fun a => f a = y)).Nonempty
  · obtain ⟨u, hu⟩ := hne
    simp only [F, Finset.mem_filter] at hu
    obtain ⟨⟨huS, hcard⟩, rfl⟩ := hu
    refine le_trans (Finset.card_le_card ?_) hcard
    intro v hv
    simp only [F, Finset.mem_filter] at hv ⊢
    exact ⟨hv.1.1, hv.2⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-- **Parameter selection of Theorem 1.3** (Lemmas 4.1, 4.2, 4.3, with the friend `c` of `b`
chosen different from `d`). -/
lemma select13 {V β γ M : Type} [DecidableEq V] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] [Fintype M] [DecidableEq M] (I : Finset V) (t : ℕ)
    (fA : V → Fin t → V → β) (fB : V → V → γ) (fm : V → V → Fin t → M) (k0 : ℕ)
    (h1 : Fintype.card M < t) (h2 : Fintype.card γ < k0)
    (h3 : k0 + k0 * (t * (2 * Fintype.card β)) < I.card) :
    ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, ∃ d ∈ I, ∃ i i' : Fin t, i ≠ i' ∧ [a, b, c, d].Nodup ∧
      fA a i c = fA a i b ∧ fB b a = fB b d ∧ fm a b i = fm a b i' := by
  obtain ⟨Is, hIs, hIscard⟩ := Finset.exists_subset_card_eq (s := I) (n := k0) (by omega)
  -- Lemma 4.1: `b` has at least two friends besides itself w.r.t. every `(w, j)`, `w ∈ I*`
  let bad : V → Fin t → Finset V := fun w j =>
    (I.erase w).filter (fun u => ((I.erase w).filter (fun v => fA w j v = fA w j u)).card ≤ 2)
  let Bad := Is.biUnion (fun w => Finset.univ.biUnion (fun j => bad w j))
  have hBad : Bad.card ≤ k0 * (t * (2 * Fintype.card β)) := by
    refine (Finset.card_biUnion_le).trans ?_
    rw [← hIscard, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ (fun w _ => ?_)
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ j ∈ (Finset.univ : Finset (Fin t)), (bad w j).card ≤ 2 * Fintype.card β :=
      fun j _ => card_filter_small_class_le _ _ _
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
    simp
  obtain ⟨b, hb⟩ : ((I \ Is) \ Bad).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff Bad (I \ Is)
    have h4 : (I \ Is).card = I.card - k0 := by rw [Finset.card_sdiff_of_subset hIs, hIscard]
    omega
  simp only [Finset.mem_sdiff] at hb
  obtain ⟨⟨hbI, hbIs⟩, hbBad⟩ := hb
  -- Lemma 4.2: two members of `I*` give `b` the same view
  obtain ⟨a, haIs, d, hdIs, had, hBad'⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Is) (t := Finset.univ) (f := fB b)
      (by rw [Finset.card_univ, hIscard]; exact h2) (fun _ _ => Finset.mem_univ _)
  -- Lemma 4.3: two indices give the same message from `b` to `a`
  obtain ⟨i, i', hii, hm⟩ := Fintype.exists_ne_map_eq_of_card_lt (fm a b) (by simpa using h1)
  -- the friend `c`
  have hba : b ≠ a := fun h => hbIs (h ▸ haIs)
  have hbd : b ≠ d := fun h => hbIs (h ▸ hdIs)
  have hclass : 2 < ((I.erase a).filter (fun v => fA a i v = fA a i b)).card := by
    by_contra hle
    push_neg at hle
    apply hbBad
    simp only [Bad, bad, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      Finset.mem_erase]
    exact ⟨a, haIs, i, ⟨hba, hbI⟩, hle⟩
  obtain ⟨c, hc⟩ : (((I.erase a).filter (fun v => fA a i v = fA a i b)).erase b |>.erase d).Nonempty := by
    rw [← Finset.card_pos]
    have h5 := Finset.pred_card_le_card_erase (s := ((I.erase a).filter (fun v => fA a i v = fA a i b)).erase b) (a := d)
    have h6 := Finset.pred_card_le_card_erase (s := (I.erase a).filter (fun v => fA a i v = fA a i b)) (a := b)
    omega
  simp only [Finset.mem_erase, Finset.mem_filter] at hc
  obtain ⟨hcd, hcb, ⟨hca, hcI⟩, hcA⟩ := hc
  refine ⟨a, hIs haIs, b, hbI, c, hcI, d, hIs hdIs, i, i', hii, ?_, hcA, hBad', hm⟩
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  exact ⟨⟨hba.symm, hca.symm, had⟩, ⟨hcb.symm, hbd⟩, hcd⟩

-- CSLib candidate: Cslib/Foundations/Combinatorics/IteratedMajority.lean (`exists_seq_sel`, `lemma_4_4`)
/-- Size needed for `k` steps of the iterated majority-colour selection with `X` colours. -/
def gSel (X : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => X * gSel X k + 1

lemma gSel_le (X : ℕ) : ∀ k, gSel X k ≤ (X + 1) ^ k
  | 0 => le_rfl
  | k + 1 => by
    have := gSel_le X k
    simp only [gSel, pow_succ]
    nlinarith [Nat.one_le_pow k (X + 1) (by omega)]

/-- **Iterated majority-colour selection** (proof of Lemma 4.4): pick `v₀`, keep the most
frequent colour class of the edges `(v₀, ·)`, and recurse. -/
lemma exists_seq_sel {α C : Type} [DecidableEq α] [Fintype C] [DecidableEq C]
    (col : α → α → C) (X : ℕ) (hX : Fintype.card C ≤ X) :
    ∀ (k : ℕ) (S : Finset α), gSel X k ≤ S.card →
      ∃ (v : Fin k → α) (cs : Fin k → C) (R : Finset α),
        (∀ i, v i ∈ S) ∧ Function.Injective v ∧ R.Nonempty ∧ R ⊆ S ∧ (∀ i, v i ∉ R) ∧
        (∀ i j, i < j → col (v i) (v j) = cs i) ∧ (∀ i, ∀ b ∈ R, col (v i) b = cs i) := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨Fin.elim0, Fin.elim0, S, fun i => i.elim0, fun i => i.elim0,
      Finset.card_pos.mp (by have : gSel X 0 = 1 := rfl; omega), subset_rfl, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro S hS
    simp only [gSel] at hS
    obtain ⟨v0, hv0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    set S' := S.erase v0
    have hS' : X * gSel X k ≤ S'.card := by
      rw [Finset.card_erase_of_mem hv0]; omega
    have hg : 1 ≤ gSel X k := by cases k <;> simp [gSel]
    obtain ⟨κ, -, hκ⟩ : ∃ κ ∈ (Finset.univ : Finset C),
        gSel X k ≤ (S'.filter (fun x => col v0 x = κ)).card := by
      by_cases hne : S'.Nonempty
      · refine Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
          (fun _ _ => Finset.mem_univ _) ?_ ?_
        · obtain ⟨x, -⟩ := hne
          exact ⟨col v0 x, Finset.mem_univ _⟩
        · rw [Finset.card_univ]
          exact le_trans (Nat.mul_le_mul_right _ hX) hS'
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne] at hS'
        simp at hS'
        have hX0 : X = 0 := by
          rcases hS' with h | h
          · exact h
          · omega
        subst hX0
        have : Fintype.card C = 0 := by omega
        exact absurd (Fintype.card_eq_zero_iff.mp this) (fun h => h.elim (col v0 v0))
    obtain ⟨v', cs', R, hv'S, hv'inj, hRne, hRS, hv'R, hcol, hcolR⟩ := ih _ hκ
    have hmem : ∀ x ∈ S'.filter (fun x => col v0 x = κ), x ∈ S ∧ x ≠ v0 ∧ col v0 x = κ := by
      intro x hx
      simp only [S', Finset.mem_filter, Finset.mem_erase] at hx
      exact ⟨hx.1.2, hx.1.1, hx.2⟩
    refine ⟨Fin.cons v0 v', Fin.cons κ cs', R, ?_, ?_, hRne, fun x hx => (hmem x (hRS hx)).1,
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hv0
      · simpa using (hmem _ (hv'S i)).1
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => simp at hij; exact absurd hij.symm (hmem _ (hv'S j)).2.1
      | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij; exact absurd hij (hmem _ (hv'S i)).2.1
        | succ j => simp at hij; rw [hv'inj hij]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro h; exact (hmem _ (hRS h)).2.1 rfl
      · simpa using hv'R i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j => simpa using (hmem _ (hv'S j)).2.2
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ j => simpa using hcol i j (Fin.succ_lt_succ_iff.mp hij)
    · intro i b hb
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using (hmem _ (hRS hb)).2.2
      · simpa using hcolR i b hb

/-- **Lemma 4.4** (abstract form): for a colouring of ordered pairs with at most `X` colours of
a set of size `≥ gSel X (2X + 1)`, there are distinct `a, b, c, d` such that
`(a, b), (a, c), (a, d), (c, b), (d, b)` have the same colour. -/
lemma lemma_4_4 {α C : Type} [DecidableEq α] [Fintype C] [DecidableEq C]
    (col : α → α → C) (X : ℕ) (hX : Fintype.card C ≤ X) (I : Finset α)
    (hI : gSel X (2 * X + 1) ≤ I.card) :
    ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, ∃ d ∈ I, [a, b, c, d].Nodup ∧ col a c = col a b ∧
      col a d = col a b ∧ col c b = col a b ∧ col d b = col a b := by
  obtain ⟨v, cs, R, hvS, hinj, hRne, hRS, hvR, hcol, hcolR⟩ := exists_seq_sel col X hX _ I hI
  obtain ⟨κ, hκ⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := cs) (n := 2)
    (by simp; omega)
  set F := Finset.univ.filter (fun x => cs x = κ)
  have hF : ∀ x ∈ F, cs x = κ := fun x hx => (Finset.mem_filter.mp hx).2
  have hF1 : F.Nonempty := Finset.card_pos.mp (by omega)
  set i1 := F.min' hF1
  have hi1 : i1 ∈ F := F.min'_mem hF1
  set F1 := F.erase i1
  have hF1' : F1.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hi1]; omega)
  set i2 := F1.min' hF1'
  have hi2 : i2 ∈ F1 := F1.min'_mem hF1'
  set F2 := F1.erase i2
  have hF2' : F2.Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hi2, Finset.card_erase_of_mem hi1]; omega)
  set i3 := F2.min' hF2'
  have hi3 : i3 ∈ F2 := F2.min'_mem hF2'
  have hi2F : i2 ∈ F := (Finset.mem_erase.mp hi2).2
  have hi3F1 : i3 ∈ F1 := (Finset.mem_erase.mp hi3).2
  have hi3F : i3 ∈ F := (Finset.mem_erase.mp hi3F1).2
  have h12 : i1 < i2 := lt_of_le_of_ne (F.min'_le _ hi2F) (Ne.symm (Finset.mem_erase.mp hi2).1)
  have h23 : i2 < i3 := lt_of_le_of_ne (F1.min'_le _ hi3F1) (Ne.symm (Finset.mem_erase.mp hi3).1)
  obtain ⟨b, hb⟩ := hRne
  have c1 := hF _ hi1
  have c2 := hF _ hi2F
  have c3 := hF _ hi3F
  refine ⟨v i1, hvS _, b, hRS hb, v i2, hvS _, v i3, hvS _, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨⟨fun h => hvR _ (h ▸ hb), fun h => h12.ne (hinj h), fun h => (h12.trans h23).ne (hinj h)⟩,
      ⟨fun h => hvR _ (h ▸ hb), fun h => hvR _ (h ▸ hb)⟩, fun h => h23.ne (hinj h)⟩
  · rw [hcol _ _ h12, hcolR _ _ hb]
  · rw [hcol _ _ (h12.trans h23), hcolR _ _ hb]
  · rw [hcolR _ _ hb, hcolR _ _ hb, c1, c2]
  · rw [hcolR _ _ hb, hcolR _ _ hb, c1, c3]

end Podc.DynamicSubgraphFinding
