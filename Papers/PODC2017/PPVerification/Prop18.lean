import Papers.PODC2017.PPVerification.Prop18T1
import Papers.PODC2017.PPVerification.Soundness

/-!
# Proposition 18: `P_thr` satisfies LayeredTermination

With `T₁ = {t : pre(t) ≠ ⦃q, r⦄, q ∈ L₀, r ∈ N₁}` and `T₂ = T \ T₁` (the paper's partition for
`c > 0`), for **every** `c` (the paper's case split on the sign of `c` is unnecessary).
-/

namespace Podc.PPVerification.Threshold

open Cslib.PopulationProtocol Cslib.TransitionSystem

variable {v : ℤ} (c : ℤ)

/-! ### Helper lemmas -/

theorem pair_eq_pair_iff {α : Type*} {a b x y : α} :
    ({a, b} : Multiset α) = {x, y} ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  simp only [Multiset.insert_eq_cons, Multiset.cons_eq_cons, Multiset.singleton_inj,
    Multiset.singleton_eq_cons_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨-, cs, ⟨h1, -⟩, h2, -⟩)
    exacts [.inl ⟨h1, h2⟩, .inr ⟨h2.symm, h1⟩]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact .inl ⟨h1, h2⟩
    · by_cases hax : a = x
      · subst h1 h2 hax; exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨hax, 0, ⟨h2, rfl⟩, h1.symm, rfl⟩

theorem fV_zero {m n : Set.Icc (-v) v} (hn : (n : ℤ) = 0) : fV m n = m := by
  have := m.2.1; have := m.2.2
  apply Subtype.ext; simp only [fV, clampV, hn]; omega

theorem gV_zero {m n : Set.Icc (-v) v} (hn : (n : ℤ) = 0) : gV m n = n := by
  have := m.2.1; have := m.2.2
  apply Subtype.ext; simp only [gV, clampV, hn]; omega

/-- The non-silent transitions of `T₂` are `(1, m, 0), (0, 0, 1) ↦ (1, m, 0), (0, 0, 0)`. -/
theorem T2_cases {t : Transition (St v)} (ht : t ∈ T2 c) :
    t.Silent ∨ ∃ m n : Set.Icc (-v) v, c ≤ m ∧ (n : ℤ) = 0 ∧
      t = mainT c (true, m, false) (false, n, true) := by
  obtain ⟨htr, m, n, hm, hn, hpre⟩ := ht
  rcases htr with ⟨hp, heq⟩ | ⟨hp, h1, h2⟩
  · right
    simp only [Transition.pre] at hpre
    rcases pair_eq_pair_iff.1 hpre with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact ⟨m, n, hm, hn, heq.trans (by rw [h1, h2])⟩
    · rw [h1] at hp; simp at hp
  · left; simp [Transition.Silent, Transition.pre, Transition.post, h1, h2]

/-- Weight: `1` on the state `(0, 0, 1)`, `0` elsewhere. -/
def wN1 (s : St v) : ℕ := if s.1 = false ∧ (s.2.1 : ℤ) = 0 ∧ s.2.2 = true then 1 else 0

theorem mainT_L0N1_post {m n : Set.Icc (-v) v} (hm : c ≤ m) (hn : (n : ℤ) = 0) :
    (mainT c (true, m, false) (false, n, true)).post = {(true, m, false), (false, n, false)} := by
  have h : ¬ ((m : ℤ) < c) := not_lt.2 hm
  simp [mainT, Transition.post, fV_zero hn, gV_zero hn, h]

theorem mainT_L0N0_silent {m n : Set.Icc (-v) v} (hm : c ≤ m) (hn : (n : ℤ) = 0) :
    (mainT c (true, m, false) (false, n, false)).Silent := by
  have h : ¬ ((m : ℤ) < c) := not_lt.2 hm
  simp [mainT, Transition.Silent, Transition.pre, Transition.post, fV_zero hn, gV_zero hn, h]

/-- `[T₁, T₂]` is an ordered partition of the transitions of `P_thr`. -/
theorem isOrderedPartition (hc : |c| + 1 ≤ v) :
    IsOrderedPartition (trans c (v := v)) [T1 c, T2 c] := by
  have hc' := abs_lt.1 (show |c| < v by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_⟩
    · let s0 : St v := (false, ⟨0, by constructor <;> omega⟩, false)
      refine ⟨⟨s0, s0, s0, s0⟩, Or.inr ⟨rfl, rfl, rfl⟩, ?_⟩
      rintro ⟨m, n, -, -, h⟩
      simp only [Transition.pre] at h
      rcases pair_eq_pair_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩ <;> simp [s0, Prod.ext_iff] at h
    · refine ⟨mainT c (true, ⟨c, by constructor <;> omega⟩, false)
        (false, ⟨0, by constructor <;> omega⟩, true), mainT_mem c rfl, ?_⟩
      exact ⟨_, _, le_rfl, rfl, rfl⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, IsEmpty.forall_iff, implies_true, and_true]
    exact Set.disjoint_left.2 fun t h1 h2 => h1.2 h2.2
  · ext t
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      Set.mem_ofPred_eq, T1, T2]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases h' : InL0N1 c t
      exacts [.inr ⟨h, h'⟩, .inl ⟨h, h'⟩]

/-- **Proposition 18, condition (a) for `T₂`.** Every execution of `P_thr[T₂]` is silent. -/
theorem t2_silent {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) :
    ∀ E : Run ((protocol c a ha).restrict (T2 c)).Step, E.Silent := by
  refine (protocol c a ha).restrict_silent_of_measure (β := ℕ) (fun C => (C.map wN1).sum) ?_
  intro t ht hns C hle
  rcases T2_cases c ht with hs | ⟨m, n, hm, hn, rfl⟩
  · exact absurd hs hns
  · have hf : (mainT c (true, m, false) (false, n, true)).Fires C (C - _ + _) := ⟨hle, rfl⟩
    have := hf.sum_map wN1
    generalize (Multiset.map wN1 (C - _ + _)).sum = X at this ⊢
    rw [mainT_L0N1_post c hm hn] at this
    simp [Transition.pre, mainT, wN1, hn] at this
    omega

/-- One non-silent `T₂`-step preserves terminality in `P_thr[T₁]`. -/
theorem terminal_T1_step {m n : Set.Icc (-v) v} (hm : c ≤ m) (hn : (n : ℤ) = 0)
    {C : Multiset (St v)} (hC : Terminal (T1 c ∪ MProtocol.idTrans) C)
    (hle : ({(true, m, false), (false, n, true)} : Multiset (St v)) ≤ C) :
    Terminal (T1 c ∪ MProtocol.idTrans)
      (C - {(true, m, false), (false, n, true)} + {(true, m, false), (false, n, false)}) := by
  have hC1 := terminal_iff_forall_silent.1 (terminal_union.1 hC).1
  refine terminal_union.2 ⟨?_, MProtocol.terminal_idTrans _⟩
  rw [terminal_iff_forall_silent]
  intro t ht hpre
  by_contra hns
  have hC' : C - {(true, m, false), (false, n, true)} + {(true, m, false), (false, n, false)} ≤
      C + {(false, n, false)} := by
    calc _ ≤ C - {(true, m, false), (false, n, true)} + {(true, m, false), (false, n, true)} +
          {(false, n, false)} := by
          rw [add_assoc]
          refine (add_le_add_iff_left _).2 ?_
          simp [Multiset.insert_eq_cons]
      _ = C + {(false, n, false)} := by rw [tsub_add_cancel_of_le hle]
  have hpre' := hpre.trans hC'
  obtain ⟨htr, hnot⟩ := ht
  rcases htr with ⟨hp, heq⟩ | ⟨hp, h1, h2⟩
  swap
  · exact hns (silent_of_mem_trans c (Or.inr ⟨hp, h1, h2⟩) hp)
  have hpn0 : t.p ≠ (false, n, false) := by intro h; rw [h] at hp; simp at hp
  by_cases hq : t.q = (false, n, false)
  · have hpC : t.p ∈ C := by
      have : t.p ∈ C + {(false, n, false)} :=
        Multiset.mem_of_le hpre' (by simp [Transition.pre])
      simpa [hpn0] using this
    by_cases hpl : t.p = (true, m, false)
    · apply hns
      rw [heq, hpl, hq]
      exact mainT_L0N0_silent c hm hn
    · have hℓC : ((true, m, false) : St v) ∈ C := Multiset.mem_of_le hle (by simp)
      have hle2 : (mainT c t.p (true, m, false)).pre ≤ C := by
        simp only [Transition.pre, mainT]
        rw [Multiset.le_iff_subset (by simp [hpl])]
        intro x hx
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hmem : mainT c t.p (true, m, false) ∈ T1 c := by
        refine ⟨mainT_mem c hp, ?_⟩
        rintro ⟨m', n', -, -, h⟩
        simp only [Transition.pre, mainT] at h
        rcases pair_eq_pair_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
        · simp [Prod.ext_iff] at h
        · rw [h] at hp; simp at hp
      have := mainT_silent c hp (hC1 _ hmem hle2)
      simp at this
  · have : t.pre ≤ C := by
      rw [Multiset.le_iff_count] at hpre' ⊢
      intro x
      have := hpre' x
      by_cases hx : x = (false, n, false)
      · subst hx
        simp [Transition.pre, Ne.symm hpn0, Ne.symm hq]
      · simpa [Multiset.count_singleton, hx] using this
    exact hns (hC1 t ⟨Or.inl ⟨hp, heq⟩, hnot⟩ this)

/-- **Proposition 18, condition (b) for `T₂`.** `P_thr[T₂]` is `T₁`-dead: from a configuration
terminal in `P_thr[T₁]`, `T₂`-steps only lead to configurations terminal in `P_thr[T₁]`. -/
theorem t2_dead {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) (C C' : Multiset (St v))
    (h : MReach ((protocol c a ha).restrict (T2 c)).T C C')
    (hC : Terminal ((protocol c a ha).restrict (T1 c)).T C) :
    Terminal ((protocol c a ha).restrict (T1 c)).T C' := by
  induction h with
  | refl => exact hC
  | tail _ hs ih =>
    obtain ⟨t, ht, hf⟩ := hs
    rcases ht with ht | ht
    · rcases T2_cases c ht with hsil | ⟨m, n, hm, hn, rfl⟩
      · rwa [hf.eq_of_silent hsil]
      · rw [hf.2, mainT_L0N1_post c hm hn]
        exact terminal_T1_step c hm hn ih hf.1
    · rwa [hf.eq_of_silent (MProtocol.silent_of_mem_idTrans ht)]

/-- **Proposition 18.** `P_thr` (any value bound `v ≥ |c| + 1`) satisfies LayeredTermination with
the ordered partition `[T₁, T₂]`. -/
theorem proposition_18_with {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) (hc : |c| + 1 ≤ v) :
    LayeredTerminationWith (protocol c a ha) [T1 c, T2 c] := by
  refine ⟨isOrderedPartition c hc, fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  obtain _ | _ | i := i
  · refine ⟨t1_silent c a ha hc, fun C C' _ _ => ?_⟩
    have h0 : layersBelow [T1 c (v := v), T2 c] 0 = ∅ := by simp [layersBelow]
    show Terminal (layersBelow _ 0 ∪ MProtocol.idTrans) C'
    rw [h0, Set.empty_union]
    exact MProtocol.terminal_idTrans _
  · refine ⟨t2_silent c a ha, fun C C' h hC => ?_⟩
    have h1 : layersBelow [T1 c (v := v), T2 c] 1 = T1 c := by ext t; simp [layersBelow]
    show Terminal (layersBelow _ 1 ∪ MProtocol.idTrans) C'
    change Terminal (layersBelow _ 1 ∪ MProtocol.idTrans) C at hC
    rw [h1] at hC ⊢
    exact t2_dead c a ha C C' h hC
  · omega

/-- **Proposition 18.** `P_thr` satisfies LayeredTermination. -/
theorem proposition_18 {Λ : Type*} [Fintype Λ] (a : Λ → ℤ) : LayeredTermination (Pthr c a) :=
  ⟨_, proposition_18_with c a _ (le_vmax c a).1⟩

end Podc.PPVerification.Threshold
