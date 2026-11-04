import Papers.PODC2015.KAtomicityVerification.Basic

/-!
# Lemma 3.8: the graph characterization of k-atomicity

`H` (satisfying Assumption 3.4) is `k`-atomic iff the write graph `G_W` has a topological
ordering `T = v₁ … v_{|V|}` in which every edge `(vᵢ, vⱼ)` of the read value graph `G_R` has
`j > i - k`.

We also provide the bridge between value orders given as lists (the paper's `T`) and value orders
given as injective *ranks* `p : V → ℕ` (positions with gaps allowed), which is how the algorithms'
correctness proofs use Lemma 3.8.
-/

set_option linter.unusedSectionVars false

namespace Podc.KAtomicityVerification

open Finset

variable {V R : Type*} [Fintype V] [DecidableEq V]

namespace History

variable (H : History V R)

/-- A value order given by an injective rank function: `G_W` edges go up, `G_R` edges go down
by less than `k`. -/
def IsKAtomicRank (k : ℕ) (p : V → ℕ) : Prop :=
  Function.Injective p ∧ (∀ a b, H.EW a b → p a < p b) ∧ (∀ a b, H.ER a b → p a < p b + k)

end History

/-! ### Lists sorted by an injective key -/

/-- Sorting the values by an injective key `p` gives a list without repetition listing every
value, along which `p` grows by at least the index difference. -/
lemma exists_sorted_list (p : V → ℕ) (hp : Function.Injective p) :
    ∃ T : List V, T.Nodup ∧ (∀ v, v ∈ T) ∧
      ∀ (i j : ℕ) (hi : i < T.length) (hj : j < T.length), i ≤ j → p T[i] + (j - i) ≤ p T[j] := by
  classical
  set T := (Finset.univ : Finset V).toList.mergeSort (fun a b => decide (p a ≤ p b)) with hT
  have hperm : T.Perm (Finset.univ : Finset V).toList := List.mergeSort_perm _ _
  have hnd : T.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
  have hmem : ∀ v, v ∈ T := fun v => hperm.mem_iff.2 (by simp)
  have hpw : T.Pairwise (fun a b => decide (p a ≤ p b) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega
    · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hlt : T.Pairwise (fun a b => p a < p b) := by
    have := hpw.and hnd
    refine this.imp ?_
    intro a b ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd (hp h) h2
  refine ⟨T, hnd, hmem, ?_⟩
  intro i j hi hj hij
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h1 := ih (by omega)
    have h2 : p T[j] < p T[j + 1] :=
      List.pairwise_iff_getElem.1 hlt j (j + 1) (by omega) hj (by omega)
    omega

namespace History

variable {H : History V R}

lemma IsKAtomicValueOrder.getElem_idxOf {k : ℕ} {T : List V} (hT : H.IsKAtomicValueOrder k T)
    (v : V) : T[T.idxOf v]'(List.idxOf_lt_length_iff.2 (hT.complete v)) = v :=
  List.getElem_idxOf _

/-- A list value order yields a rank value order (`p = idxOf`). -/
lemma IsKAtomicValueOrder.rank {k : ℕ} {T : List V} (hT : H.IsKAtomicValueOrder k T) :
    H.IsKAtomicRank k (fun v => T.idxOf v) := by
  have hl : ∀ v, T.idxOf v < T.length := fun v => List.idxOf_lt_length_iff.2 (hT.complete v)
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    have := hT.getElem_idxOf a
    have := hT.getElem_idxOf b
    simp only at h
    grind
  · intro a b h
    have := hT.topo (T.idxOf a) (T.idxOf b) (hl a) (hl b)
    simp only [hT.getElem_idxOf] at this
    exact this h
  · intro a b h
    have := hT.back (T.idxOf a) (T.idxOf b) (hl a) (hl b)
    simp only [hT.getElem_idxOf] at this
    exact this h

/-- A rank value order yields a list value order (sort by the rank). -/
lemma IsKAtomicRank.exists_valueOrder {k : ℕ} {p : V → ℕ} (hp : H.IsKAtomicRank k p) :
    ∃ T, H.IsKAtomicValueOrder k T := by
  obtain ⟨T, hnd, hmem, hmono⟩ := exists_sorted_list p hp.1
  refine ⟨T, ⟨hnd, hmem, ?_, ?_⟩⟩
  · intro i j hi hj h
    have := hp.2.1 _ _ h
    by_contra hij
    have := hmono j i hj hi (by omega)
    omega
  · intro i j hi hj h
    have := hp.2.2 _ _ h
    by_contra hij
    have := hmono j i hj hi (by omega)
    omega

lemma exists_valueOrder_iff_rank {k : ℕ} :
    (∃ T, H.IsKAtomicValueOrder k T) ↔ ∃ p, H.IsKAtomicRank k p :=
  ⟨fun ⟨_, hT⟩ => ⟨_, hT.rank⟩, fun ⟨_, hp⟩ => hp.exists_valueOrder⟩

/-- Every finite history has a topological ordering of its write graph. -/
lemma exists_topoOrder : ∃ T, H.IsTopoOrder T := by
  obtain ⟨T, hnd, hmem, hmono⟩ := exists_sorted_list (V := V)
    (fun v => (Fintype.equivFin V v : ℕ) + (Fintype.card V) * H.f (.inl v)) (by
      intro a b h
      simp only at h
      have ha := (Fintype.equivFin V a).2
      have hb := (Fintype.equivFin V b).2
      have : H.f (.inl a) = H.f (.inl b) := by
        rcases lt_trichotomy (H.f (.inl a)) (H.f (.inl b)) with h' | h' | h'
        · have := Nat.mul_le_mul_left (Fintype.card V) (Nat.succ_le_of_lt h')
          rw [Nat.mul_succ] at this; omega
        · exact h'
        · have := Nat.mul_le_mul_left (Fintype.card V) (Nat.succ_le_of_lt h')
          rw [Nat.mul_succ] at this; omega
      rw [this] at h
      exact (Fintype.equivFin V).injective (Fin.ext (by omega)))
  refine ⟨T, hnd, hmem, ?_⟩
  intro i j hi hj h
  by_contra hij
  have h1 := hmono j i hj hi (by omega)
  have h2 : H.f (.inl T[i]) < H.f (.inl T[j]) := lt_trans h (H.s_lt_f _)
  have ha := (Fintype.equivFin V T[i]).2
  have := Nat.mul_le_mul_left (Fintype.card V) (Nat.succ_le_of_lt h2)
  rw [Nat.mul_succ] at this
  omega

/-! ### Lemma 3.8 -/

/-- A strict order pulled back along an injective map into a linear order is a strict total
order. -/
lemma isStrictTotalOrder_of_injective {α β : Type*} [LinearOrder β] (g : α → β)
    (hg : Function.Injective g) : IsStrictTotalOrder α (fun a b => g a < g b) where
  trichotomous _ _ h1 h2 := hg (le_antisymm (not_lt.1 h2) (not_lt.1 h1))
  irrefl a := lt_irrefl (g a)
  trans _ _ _ := lt_trans

open Classical in
/-- The key used to build a `k`-atomic total order from a value order with ranks `p`: writes at
`(p v, 0, 0)`, a read `r` right after the latest write that must precede it, at
`(q r, 1, s r)`, ties broken by an enumeration `e` of the operations. -/
noncomputable def opKey [Fintype R] (H : History V R) (p : V → ℕ) (x : V ⊕ R) :
    ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  match x with
  | .inl v => toLex (p v, toLex (0, toLex (0, (Fintype.equivFin (V ⊕ R) x : ℕ))))
  | .inr r => toLex (max (p (H.val r))
        ((Finset.univ.filter (fun u => H.hb (.inl u) (.inr r))).sup p),
      toLex (1, toLex (H.s (.inr r), (Fintype.equivFin (V ⊕ R) x : ℕ))))

/-- **Lemma 3.8** of [Golab–Li–López-Ortiz–Nishimura]. Under Assumption 3.4 (in force throughout
the paper) and for `k ≥ 1`, a history `H` is `k`-atomic iff its write graph `G_W` has a
topological ordering `T = v₁ … v_{|V|}` such that every edge `(vᵢ, vⱼ)` of the read value graph
`G_R` satisfies `j > i - k`. -/
theorem kAtomic_iff_exists_valueOrder [Fintype R] (hA : H.Assumption34) {k : ℕ} (hk : 0 < k) :
    H.KAtomic k ↔ ∃ T, H.IsKAtomicValueOrder k T := by
  classical
  rw [exists_valueOrder_iff_rank]
  constructor
  · rintro ⟨lt, hto, hext, hread⟩
    have := hto
    let p : V → ℕ := fun v => (univ.filter (fun u => lt (.inl u) (.inl v))).card
    have hp_lt : ∀ a b, lt (.inl a) (.inl b) → p a < p b := by
      intro a b hab
      apply Finset.card_lt_card
      refine ⟨fun u hu => ?_, fun hsub => ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at hu ⊢
        exact _root_.trans hu hab
      · have := hsub (by simpa using hab)
        simp only [mem_filter, mem_univ, true_and] at this
        exact irrefl _ this
    have hp_inj : Function.Injective p := by
      intro a b h
      by_contra hne
      rcases trichotomous_of lt (Sum.inl a : V ⊕ R) (Sum.inl b) with h' | h' | h'
      · exact absurd h (hp_lt _ _ h').ne
      · exact hne (Sum.inl_injective h')
      · exact absurd h (hp_lt _ _ h').ne'
    refine ⟨p, hp_inj, fun a b h => hp_lt a b (hext _ _ h), ?_⟩
    rintro a b ⟨hne, r, rfl, har⟩
    rcases trichotomous_of lt (Sum.inl a : V ⊕ R) (Sum.inl (H.val r)) with h' | h' | h'
    · have := hp_lt _ _ h'; omega
    · exact absurd (Sum.inl_injective h') hne
    · -- `w(val r) <_T w(a) <_T r`: count the writes in between
      set b := H.val r
      have har' : lt (.inl a) (.inr r) := hext _ _ har
      let F := insert a (univ.filter (fun u => lt (.inl b) (.inl u) ∧ lt (.inl u) (.inl a)))
      have hF : (↑F : Set V) ⊆
          {v : V | lt (.inl (H.val r)) (.inl v) ∧ lt (.inl v) (.inr r)} := by
        intro u hu
        simp only [F, coe_insert, coe_filter, mem_univ, true_and, Set.mem_insert_iff,
          Set.mem_ofPred_eq] at hu
        rcases hu with rfl | ⟨h1, h2⟩
        · exact ⟨h', har'⟩
        · exact ⟨h1, _root_.trans h2 har'⟩
      have hFcard : F.card < k := by
        have := Set.ncard_le_ncard hF (Set.toFinite _)
        rw [Set.ncard_coe_finset] at this
        exact lt_of_le_of_lt this (hread r).2
      have hFa : a ∉ univ.filter (fun u => lt (.inl b) (.inl u) ∧ lt (.inl u) (.inl a)) := by
        simp only [mem_filter, mem_univ, true_and, not_and]
        exact fun _ => irrefl _
      rw [Finset.card_insert_of_notMem hFa] at hFcard
      have hsub : univ.filter (fun u => lt (.inl u) (.inl a)) ⊆
          insert b ((univ.filter (fun u => lt (.inl u) (.inl b))) ∪
            univ.filter (fun u => lt (.inl b) (.inl u) ∧ lt (.inl u) (.inl a))) := by
        intro u hu
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_union] at hu ⊢
        rcases trichotomous_of lt (Sum.inl u : V ⊕ R) (Sum.inl b) with h'' | h'' | h''
        · exact Or.inr (Or.inl h'')
        · exact Or.inl (Sum.inl_injective h'')
        · exact Or.inr (Or.inr ⟨h'', hu⟩)
      have := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le b ((univ.filter (fun u => lt (.inl u) (.inl b))) ∪
            univ.filter (fun u => lt (.inl b) (.inl u) ∧ lt (.inl u) (.inl a)))
      have h3 := Finset.card_union_le (univ.filter (fun u => lt (.inl u) (.inl b)))
        (univ.filter (fun u => lt (.inl b) (.inl u) ∧ lt (.inl u) (.inl a)))
      show p a < p b + k
      simp only [p]
      omega
  · rintro ⟨p, hp_inj, hEW, hER⟩
    set key := opKey H p
    have hkey : Function.Injective key := by
      intro x y h
      apply (Fintype.equivFin (V ⊕ R)).injective
      apply Fin.ext
      cases x <;> cases y <;> simp [key, opKey] at h <;> grind
    have hto := isStrictTotalOrder_of_injective key hkey
    let q : R → ℕ := fun r => max (p (H.val r))
        ((Finset.univ.filter (fun u => H.hb (.inl u) (.inr r))).sup p)
    have hk_w : ∀ u v, key (.inl u) < key (.inl v) ↔ p u < p v := by
      intro u v
      simp only [key, opKey, Prod.Lex.toLex_lt_toLex]
      constructor
      · rintro (h | ⟨h1, h2 | ⟨_, h3 | ⟨_, h4⟩⟩⟩)
        · exact h
        · omega
        · omega
        · exact absurd (hp_inj h1) (fun h => by subst h; omega)
      · intro h; exact Or.inl h
    have hk_wr : ∀ u r, key (.inl u) < key (.inr r) ↔ p u ≤ q r := by
      intro u r
      simp only [key, opKey, Prod.Lex.toLex_lt_toLex, q]
      constructor
      · rintro (h | ⟨h1, _⟩) <;> omega
      · intro h
        rcases h.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inl (by omega)⟩
    have hk_rw : ∀ r v, q r < p v → key (.inr r) < key (.inl v) := by
      intro r v h
      simp only [key, opKey, Prod.Lex.toLex_lt_toLex, q] at h ⊢
      exact Or.inl h
    have hk_rr : ∀ r r', q r ≤ q r' → H.s (.inr r) < H.s (.inr r') →
        key (.inr r) < key (.inr r') := by
      intro r r' h1 h2
      simp only [key, opKey, Prod.Lex.toLex_lt_toLex, q] at h1 ⊢
      rcases h1.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Or.inr ⟨trivial, Or.inl h2⟩⟩
    have hq_ge : ∀ r u, H.hb (.inl u) (.inr r) → p u ≤ q r := fun r u h =>
      le_max_of_le_right (Finset.le_sup (f := p) (by simpa using h))
    have hq_val : ∀ r, p (H.val r) ≤ q r := fun r => le_max_left _ _
    have hq_lt : ∀ r v, H.hb (.inr r) (.inl v) → q r < p v := by
      intro r v h
      apply max_lt
      · apply hEW
        show H.f _ < H.s _
        exact lt_trans (hA r) h
      · rw [Finset.sup_lt_iff (by
          have := hEW (H.val r) v (lt_trans (hA r) h)
          rw [Nat.bot_eq_zero]; omega)]
        intro u hu
        simp only [mem_filter, mem_univ, true_and] at hu
        exact hEW _ _ (hb_trans hu h)
    refine ⟨fun a b => key a < key b, hto, ?_, ?_⟩
    · intro a b h
      rcases a with u | r <;> rcases b with v | r'
      · exact (hk_w u v).2 (hEW u v h)
      · exact (hk_wr u r').2 (hq_ge r' u h)
      · exact hk_rw r v (hq_lt r v h)
      · apply hk_rr r r'
        · apply max_le
          · apply hq_ge
            show H.f _ < H.s _
            exact lt_trans (hA r) h
          · apply Finset.sup_le
            intro u hu
            simp only [mem_filter, mem_univ, true_and] at hu
            exact hq_ge r' u (hb_trans hu h)
        · exact lt_trans (H.s_lt_f _) h
    · intro r
      refine ⟨(hk_wr _ _).2 (hq_val r), ?_⟩
      -- the writes between `w(val r)` and `r` have ranks in `(p (val r), q r]`
      set b := H.val r
      have hsub : {v : V | key (.inl b) < key (.inl v) ∧ key (.inl v) < key (.inr r)} ⊆
          ↑(univ.filter (fun v => p b < p v ∧ p v ≤ q r)) := by
        intro v hv
        simp only [Set.mem_ofPred_eq, hk_w, hk_wr] at hv
        simpa using hv
      refine lt_of_le_of_lt (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
      rw [Set.ncard_coe_finset]
      have hcard : (univ.filter (fun v => p b < p v ∧ p v ≤ q r)).card ≤ q r - p b := by
        rw [← Nat.card_Ioc]
        apply Finset.card_le_card_of_injOn p
        · intro v hv
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
          simp [hv.1, hv.2]
        · exact hp_inj.injOn
      by_cases hqb : q r = p b
      · omega
      · -- the maximum is attained by some `u` with `w(u) <_H r`, giving a `G_R` edge `(u, b)`
        have hne : (univ.filter (fun u => H.hb (.inl u) (.inr r))).Nonempty := by
          by_contra h
          rw [Finset.not_nonempty_iff_eq_empty] at h
          simp [q, h] at hqb
          exact hqb rfl
        obtain ⟨u, hu, hu'⟩ := Finset.exists_mem_eq_sup _ hne p
        simp only [mem_filter, mem_univ, true_and] at hu
        have hqu : q r = p u := by
          simp only [q, ← hu']
          exact max_eq_right (by
            by_contra h; push Not at h; exact hqb (max_eq_left h.le))
        by_cases hub : u = b
        · subst hub; omega
        · have := hER u b ⟨hub, r, rfl, hu⟩
          omega

end History

end Podc.KAtomicityVerification
