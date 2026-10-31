import Papers.PODC2018.PartialReplicationCausal.Chain

/-!
# Preservation of the invariant

`Inv X s` holds initially and is preserved by both kinds of steps; hence it holds in every
reachable state (`Inv.of_reachable`). The only non-routine part is safety after an `apply` step,
which is `deps_applied` (`Chain.lean`).
-/

namespace Podc.PartialReplicationCausal

open Classical

variable {ι Reg : Type*} {X : ι → Set Reg} {s : State ι Reg}

/-! ### Unfolding the steps -/

section write

variable {i : ι} {x : Reg}

@[simp] lemma write_n : (s.write X i x).n = s.n + 1 := rfl

lemma write_log_of_lt {c : ℕ} (hc : c < s.n) : (s.write X i x).log c = s.log c :=
  Function.update_of_ne (by omega) _ _

@[simp] lemma write_log_self :
    (s.write X i x).log s.n = ⟨i, x, incr X (s.τ i) i x, s.app i⟩ :=
  Function.update_self _ _ _

lemma write_τ (r : ι) :
    (s.write X i x).τ r = if r = i then incr X (s.τ i) i x else s.τ r := by
  simp only [State.write, Function.update_apply]

lemma write_app (r : ι) :
    (s.write X i x).app r = if r = i then insert s.n (s.app i) else s.app r := by
  simp only [State.write, Function.update_apply]

lemma write_cnt_le {j k : ι} {a : ℕ} (ha : a ≤ s.n) :
    cnt X (s.write X i x) j k a = cnt X s j k a :=
  cnt_congr (fun c hc => write_log_of_lt (by omega)) j k

lemma write_cnt_new (j k : ι) :
    cnt X (s.write X i x) j k (s.n + 1) = cnt X s j k s.n + if i = j ∧ x ∈ X k then 1 else 0 := by
  rw [cnt_succ, write_cnt_le le_rfl, write_log_self]

lemma le_incr (τi : ι → ι → ℕ) (j k : ι) : τi j k ≤ incr X τi i x j k := by
  unfold incr; split_ifs <;> omega

end write

section apply

variable {i : ι} {u : ℕ}

@[simp] lemma apply_n : (s.apply X i u).n = s.n := rfl

@[simp] lemma apply_log : (s.apply X i u).log = s.log := rfl

lemma apply_τ (r : ι) : (s.apply X i u).τ r =
    if r = i then merge X (s.τ i) i (s.log u).src (s.log u).ts else s.τ r := by
  simp only [State.apply, Function.update_apply]

lemma apply_app (r : ι) :
    (s.apply X i u).app r = if r = i then insert u (s.app i) else s.app r := by
  simp only [State.apply, Function.update_apply]

lemma apply_hb : HB (s.apply X i u) = HB s := rfl

lemma apply_cnt (j k : ι) (a : ℕ) : cnt X (s.apply X i u) j k a = cnt X s j k a := rfl

lemma le_merge (τi : ι → ι → ℕ) (k : ι) (T : ι → ι → ℕ) (a b : ι) :
    τi a b ≤ merge X τi i k T a b := by
  unfold merge; split_ifs <;> omega

end apply

namespace Inv

/-! ### Initial states -/

theorem init (hs : IsInit s) : Inv X s := by
  obtain ⟨hn, hτ, happ⟩ := hs
  have happ : ∀ i c, c ∉ s.app i := by intro i c; rw [happ]; simp
  have hcnt : ∀ j k, cnt X s j k s.n = 0 := by intro j k; simp [cnt, hn]
  refine ⟨fun i c hc => absurd hc (happ _ _), fun i c hc => absurd hc (happ _ _),
    fun a ha => by omega, fun a ha => by omega, fun a ha => by omega, fun a ha => by omega,
    fun a ha => by omega, fun a ha => by omega, fun i b hb => absurd hb (happ _ _),
    fun i c hc => absurd hc (happ _ _), fun a ha => by omega, ?_, fun a ha => by omega, ?_, ?_,
    fun a ha => by omega⟩
  · intro i k _; rw [hτ, hcnt]
  · intro i j _ _ c hc; omega
  · intro r e₁ e₂ _ h; rw [hτ] at h; exact absurd h (lt_irrefl 0)

variable (h : Inv X s)
include h

lemma τ_le_cnt {r e₁ e₂ : ι} (he : TsEdge X r e₁ e₂) : s.τ r e₁ e₂ ≤ cnt X s e₁ e₂ s.n := by
  rcases Nat.eq_zero_or_pos (s.τ r e₁ e₂) with h0 | hpos
  · omega
  obtain ⟨c, hc, -, -, hcnt, -⟩ := h.τ_wit r e₁ e₂ he hpos
  rw [← hcnt]; exact cnt_mono s e₁ e₂ (by omega)

lemma ts_le_cnt {a : ℕ} (ha : a < s.n) {e₁ e₂ : ι} (he : TsEdge X (s.log a).src e₁ e₂) :
    (s.log a).ts e₁ e₂ ≤ cnt X s e₁ e₂ s.n := by
  rcases Nat.eq_zero_or_pos ((s.log a).ts e₁ e₂) with h0 | hpos
  · omega
  obtain ⟨c, hc, -, -, hcnt, -⟩ := h.ts_wit a ha e₁ e₂ he hpos
  rw [← hcnt]; exact cnt_mono s e₁ e₂ (by omega)

/-! ### Write steps -/

section write

variable {i : ι} {x : Reg}

lemma write_hb_old {a b : ℕ} (hb : b < s.n) : HB (s.write X i x) a b ↔ HB s a b :=
  ⟨fun hab => hb_back (fun _ hc => write_log_of_lt hc) (fun c hc d hd => h.pre_lt_n hc hd) hab hb,
    hb_mono (by simp) (fun _ hc => write_log_of_lt hc)⟩

lemma write_hb_new {a : ℕ} :
    HB (s.write X i x) a s.n → a ∈ s.app i ∨ ∃ c ∈ s.app i, HB s a c := by
  intro hab
  rcases Relation.TransGen.tail'_iff.1 hab with ⟨c, hac, hc⟩
  rw [write_log_self] at hc
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hac with rfl | hac
  · exact Or.inl hc.2
  · exact Or.inr ⟨c, hc.2, (h.write_hb_old (h.app_lt _ _ hc.2)).1 hac⟩

theorem write (hx : x ∈ X i) : Inv X (s.write X i x) := by
  have hlog : ∀ {c}, c < s.n → (s.write X i x).log c = s.log c := fun hc => write_log_of_lt hc
  -- the new update is in the causal past of `i`'s applied set
  constructor
  · -- app_lt
    intro r c hc
    rw [write_app] at hc; split_ifs at hc with hr
    · rcases Set.mem_insert_iff.1 hc with rfl | hc
      · simp
      · have := h.app_lt _ _ hc; simp; omega
    · have := h.app_lt _ _ hc; simp; omega
  · -- app_reg
    intro r c hc
    rw [write_app] at hc; split_ifs at hc with hr
    · rcases Set.mem_insert_iff.1 hc with rfl | hc
      · simp [hr, hx]
      · rw [hlog (h.app_lt _ _ hc)]; exact hr ▸ h.app_reg _ _ hc
    · rw [hlog (h.app_lt _ _ hc)]; exact h.app_reg _ _ hc
  · -- own
    intro a ha
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt, write_app]; split_ifs with hr
      · exact Set.mem_insert_of_mem _ (hr ▸ h.own a hlt)
      · exact h.own a hlt
    · obtain rfl : a = s.n := by simp at ha; omega
      simp [write_app]
  · -- pre_lt
    intro a ha c hc
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt] at hc; exact h.pre_lt a hlt c hc
    · obtain rfl : a = s.n := by simp at ha; omega
      simp only [write_log_self] at hc; exact h.app_lt _ _ hc
  · -- pre_app
    intro a ha c hc
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt] at hc ⊢; rw [write_app]; split_ifs with hr
      · exact Set.mem_insert_of_mem _ (hr ▸ h.pre_app a hlt hc)
      · exact h.pre_app a hlt hc
    · obtain rfl : a = s.n := by simp at ha; omega
      simp only [write_log_self] at hc ⊢
      simp [write_app, hc]
  · -- pre_own
    intro a ha c hca hsrc
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt, hlog (by omega)] at hsrc; rw [hlog hlt]; exact h.pre_own a hlt c hca hsrc
    · obtain rfl : a = s.n := by simp at ha; omega
      rw [hlog hca] at hsrc; simp only [write_log_self] at hsrc ⊢
      exact hsrc ▸ h.own c hca
  · -- pre_mono
    intro a ha c hca hsrc
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt, hlog (by omega)] at hsrc ⊢; exact h.pre_mono a hlt c hca hsrc
    · obtain rfl : a = s.n := by simp at ha; omega
      rw [hlog hca] at hsrc ⊢; simp only [write_log_self] at hsrc ⊢
      exact hsrc ▸ h.pre_app c hca
  · -- pre_safe
    intro a ha c hc b hb hbc
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt] at hc hb ⊢
      have hcn := h.pre_lt_n hlt hc
      have hbc' := (h.write_hb_old hcn).1 hbc
      rw [hlog ((h.hb_lt hbc').trans hcn)] at hb
      exact h.pre_safe a hlt c hc b hb hbc'
    · obtain rfl : a = s.n := by simp at ha; omega
      simp only [write_log_self] at hc hb ⊢
      have hcn := h.app_lt _ _ hc
      have hbc' := (h.write_hb_old hcn).1 hbc
      rw [hlog ((h.hb_lt hbc').trans hcn)] at hb
      exact h.safe i c hc b hb hbc'
  · -- safe
    intro r c hc b hb hbc
    have hcn : c < s.n + 1 := by
      have := hb_lt_n hbc; simpa using this
    rw [write_app] at hc ⊢
    -- `b` happened before `c`, so it is an old update
    by_cases hcs : c = s.n
    · subst hcs
      have hr : r = i := by
        split_ifs at hc with hr
        · exact hr
        · exact absurd (h.app_lt _ _ hc) (lt_irrefl _)
      subst hr
      simp only at hc ⊢
      rcases h.write_hb_new hbc with hb' | ⟨d, hd, hbd⟩
      · exact Set.mem_insert_of_mem _ hb'
      · rw [hlog ((h.hb_lt hbd).trans (h.app_lt _ _ hd))] at hb
        exact Set.mem_insert_of_mem _ (h.safe r d hd b hb hbd)
    · have hcn' : c < s.n := by omega
      have hbc' := (h.write_hb_old hcn').1 hbc
      rw [hlog ((h.hb_lt hbc').trans hcn')] at hb
      split_ifs at hc ⊢ with hr
      · subst hr
        rcases Set.mem_insert_iff.1 hc with rfl | hc
        · exact absurd rfl hcs
        · exact Set.mem_insert_of_mem _ (h.safe r c hc b hb hbc')
      · exact h.safe r c hc b hb hbc'
  · -- τ_app
    intro r c hc e₁ e₂ he₁ he₂
    rw [write_app] at hc; rw [write_τ]
    split_ifs at hc ⊢ with hr
    · subst hr
      rcases Set.mem_insert_iff.1 hc with rfl | hc
      · simp
      · rw [hlog (h.app_lt _ _ hc)] at he₂ ⊢
        exact (h.τ_app r c hc e₁ e₂ he₁ he₂).trans (le_incr _ _ _)
    · rw [hlog (h.app_lt _ _ hc)] at he₂ ⊢
      exact h.τ_app r c hc e₁ e₂ he₁ he₂
  · -- ts_pre
    intro a ha c hc e₁ e₂ he₁ he₂
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt] at hc he₁ ⊢
      rw [hlog (h.pre_lt_n hlt hc)] at he₂ ⊢
      exact h.ts_pre a hlt c hc e₁ e₂ he₁ he₂
    · obtain rfl : a = s.n := by simp at ha; omega
      simp only [write_log_self] at hc he₁ ⊢
      rw [hlog (h.app_lt _ _ hc)] at he₂ ⊢
      exact (h.τ_app i c hc e₁ e₂ he₁ he₂).trans (le_incr _ _ _)
  · -- τ_own
    intro r k hrk
    rw [write_τ, write_n, write_cnt_new]
    by_cases hr : r = i
    · subst hr
      simp only [ite_true, incr, tsEdge_self_iff.2 hrk, true_and]
      rw [h.τ_own r k hrk]
      by_cases hxk : x ∈ X k <;> simp [hxk]
    · simp only [hr, ite_false, Ne.symm hr, false_and]; simpa using h.τ_own r k hrk
  · -- ts_own
    intro a ha k hk hak
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt] at hk hak ⊢
      rw [write_cnt_le (by omega)]
      exact h.ts_own a hlt k hk hak
    · obtain rfl : a = s.n := by simp at ha; omega
      simp only [write_log_self] at hk hak ⊢
      rw [write_cnt_new]
      simp only [incr, tsEdge_self_iff.2 hk, hak, ite_true, and_self]
      rw [h.τ_own i k hk]
  · -- count
    intro r j hjr hjr' c hc hcj hcr
    rw [write_app, write_τ]
    by_cases hcs : c = s.n
    · subst hcs
      simp only [write_log_self] at hcj hcr
      subst hcj
      have hri : r ≠ (⟨i, x, incr X (s.τ i) i x, s.app i⟩ : Update ι Reg).src := hjr.symm
      simp only at hri
      simp only [hri, ite_false, write_cnt_new, true_and, hcr, ite_true]
      have := h.τ_le_cnt (tsEdge_in_iff.2 hjr')
      constructor
      · intro hc'; exact absurd (h.app_lt _ _ hc') (lt_irrefl _)
      · intro hle; omega
    · have hcn : c < s.n := by simp at hc; omega
      rw [hlog hcn] at hcj hcr
      rw [write_cnt_le (by omega)]
      split_ifs with hr
      · subst hr
        have hincr : incr X (s.τ r) r x j r = s.τ r j r := by
          simp only [incr, hjr, false_and, and_false, ite_false]
        rw [hincr, Set.mem_insert_iff, ← h.count r j hjr hjr' c hcn hcj hcr]
        exact ⟨fun h' => h'.resolve_left hcs, Or.inr⟩
      · exact h.count r j hjr hjr' c hcn hcj hcr
  · -- τ_wit
    intro r e₁ e₂ he hpos
    rw [write_τ] at hpos ⊢
    split_ifs at hpos ⊢ with hr
    · subst hr
      by_cases hinc : TsEdge X r e₁ e₂ ∧ e₁ = r ∧ x ∈ X e₂
      · obtain ⟨-, rfl, hxe⟩ := hinc
        refine ⟨s.n, by simp, by simp, by simpa using hxe, ?_, ?_⟩
        · rw [write_cnt_new]
          simp only [incr, he, hxe, ite_true, and_self]
          rw [h.τ_own e₁ e₂ he.1]
        · left; simp [write_app]
      · have hval : incr X (s.τ r) r x e₁ e₂ = s.τ r e₁ e₂ := by simp only [incr, hinc, ite_false]
        rw [hval] at hpos ⊢
        obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.τ_wit r e₁ e₂ he hpos
        refine ⟨c, by simp; omega, by rw [hlog hc]; exact hc1, by rw [hlog hc]; exact hc2,
          by rw [write_cnt_le (by omega)]; exact hc3, ?_⟩
        simp only [write_app]
        rcases hc4 with hc4 | ⟨d, hd, hcd⟩
        · exact Or.inl (Set.mem_insert_of_mem _ hc4)
        · exact Or.inr ⟨d, Set.mem_insert_of_mem _ hd,
            (h.write_hb_old (h.app_lt _ _ hd)).2 hcd⟩
    · obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.τ_wit r e₁ e₂ he hpos
      refine ⟨c, by simp; omega, by rw [hlog hc]; exact hc1, by rw [hlog hc]; exact hc2,
        by rw [write_cnt_le (by omega)]; exact hc3, ?_⟩
      simp only [write_app, hr, ite_false]
      rcases hc4 with hc4 | ⟨d, hd, hcd⟩
      · exact Or.inl hc4
      · exact Or.inr ⟨d, hd, (h.write_hb_old (h.app_lt _ _ hd)).2 hcd⟩
  · -- ts_wit
    intro a ha e₁ e₂ he hpos
    rcases Nat.lt_or_ge a s.n with hlt | hge
    · rw [hlog hlt] at he hpos ⊢
      obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.ts_wit a hlt e₁ e₂ he hpos
      refine ⟨c, by simp; omega, by rw [hlog hc]; exact hc1, by rw [hlog hc]; exact hc2,
        by rw [write_cnt_le (by omega)]; exact hc3, ?_⟩
      rcases hc4 with rfl | hc4
      · exact Or.inl rfl
      · exact Or.inr ((h.write_hb_old hlt).2 hc4)
    · obtain rfl : a = s.n := by simp at ha; omega
      simp only [write_log_self] at he hpos ⊢
      by_cases hinc : TsEdge X i e₁ e₂ ∧ e₁ = i ∧ x ∈ X e₂
      · obtain ⟨-, rfl, hxe⟩ := hinc
        refine ⟨s.n, by simp, by simp, by simpa using hxe, ?_, Or.inl rfl⟩
        rw [write_cnt_new]
        simp only [incr, he, hxe, ite_true, and_self]
        rw [h.τ_own e₁ e₂ he.1]
      · have hval : incr X (s.τ i) i x e₁ e₂ = s.τ i e₁ e₂ := by simp only [incr, hinc, ite_false]
        rw [hval] at hpos ⊢
        obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.τ_wit i e₁ e₂ he hpos
        refine ⟨c, by simp; omega, by rw [hlog hc]; exact hc1, by rw [hlog hc]; exact hc2,
          by rw [write_cnt_le (by omega)]; exact hc3, Or.inr ?_⟩
        rcases hc4 with hc4 | ⟨d, hd, hcd⟩
        · exact .single ⟨by simp, by simpa using hc4⟩
        · exact .tail ((h.write_hb_old (h.app_lt _ _ hd)).2 hcd) ⟨by simp, by simpa using hd⟩

end write

/-! ### Apply steps -/

theorem apply {i : ι} {u : ℕ} (hu : Enabled X s i u) : Inv X (s.apply X i u) := by
  obtain ⟨hun, hki, hux, hunapp, hready⟩ := hu
  constructor
  · intro r c hc
    rw [apply_app] at hc; split_ifs at hc
    · rcases Set.mem_insert_iff.1 hc with rfl | hc
      · exact hun
      · exact h.app_lt _ _ hc
    · exact h.app_lt _ _ hc
  · intro r c hc
    rw [apply_app] at hc; split_ifs at hc with hr
    · subst hr
      rcases Set.mem_insert_iff.1 hc with rfl | hc
      · exact hux
      · exact h.app_reg _ _ hc
    · exact h.app_reg _ _ hc
  · intro a ha
    rw [apply_app]; split_ifs with hr
    · exact Set.mem_insert_of_mem _ (hr ▸ h.own a ha)
    · exact h.own a ha
  · exact h.pre_lt
  · intro a ha c hc
    rw [apply_app]; split_ifs with hr
    · exact Set.mem_insert_of_mem _ (hr ▸ h.pre_app a ha hc)
    · exact h.pre_app a ha hc
  · exact h.pre_own
  · exact h.pre_mono
  · exact h.pre_safe
  · intro r c hc b hb hbc
    rw [apply_app] at hc ⊢
    split_ifs at hc ⊢ with hr
    · subst hr
      rcases Set.mem_insert_iff.1 hc with rfl | hc
      · exact Set.mem_insert_of_mem _
          (deps_applied h ⟨hun, hki, hux, hunapp, hready⟩ hb hbc)
      · exact Set.mem_insert_of_mem _ (h.safe r c hc b hb hbc)
    · exact h.safe r c hc b hb hbc
  · intro r c hc e₁ e₂ he₁ he₂
    simp only [apply_log] at he₂ ⊢
    rw [apply_app] at hc; rw [apply_τ]
    split_ifs at hc ⊢ with hr
    · subst hr
      rcases Set.mem_insert_iff.1 hc with rfl | hc
      · simp only [merge, he₁, he₂, and_self, ite_true]; exact le_max_right _ _
      · exact (h.τ_app r c hc e₁ e₂ he₁ he₂).trans (le_merge _ _ _ _ _)
    · exact h.τ_app r c hc e₁ e₂ he₁ he₂
  · exact h.ts_pre
  · intro r k' hrk
    rw [apply_τ, apply_cnt]
    split_ifs with hr
    · subst hr
      unfold merge
      split_ifs with hm
      · rw [h.τ_own r k' hrk]
        exact max_eq_left (h.ts_le_cnt hun hm.2)
      · exact h.τ_own r k' hrk
    · exact h.τ_own r k' hrk
  · exact h.ts_own
  · intro r j hjr hjr' c hc hcj hcr
    simp only [apply_log, apply_n] at hc hcj hcr
    rw [apply_app, apply_τ, apply_cnt]
    split_ifs with hr
    · subst hr
      rw [Set.mem_insert_iff, h.count r j hjr hjr' c hc hcj hcr]
      unfold merge
      by_cases hjk : j = (s.log u).src
      · subst hjk
        have hkk : TsEdge X (s.log u).src (s.log u).src r := tsEdge_self_iff.2 hjr'
        rw [ite_eq_left ⟨tsEdge_in_iff.2 hjr', hkk⟩]
        have h1 := hready.1
        have h2 := h.ts_own u hun r hjr' hux
        rw [max_eq_right (by omega), h2]
        constructor
        · rintro (rfl | hle)
          · exact le_rfl
          · omega
        · intro hle
          rcases Nat.lt_or_ge (cnt X s (s.log u).src r (c + 1)) (cnt X s (s.log u).src r (u + 1))
            with hlt | hge
          · right; omega
          · left; exact eq_of_cnt_eq s ⟨hcj, hcr⟩ ⟨rfl, hux⟩ (by omega)
      · have hcu : c ≠ u := fun hcu => hjk (hcu ▸ hcj).symm
        simp only [hcu, false_or]
        split_ifs with hm
        · rw [max_eq_left (hready.2 j hjr hjk hm.1 hm.2)]
        · exact Iff.rfl
    · exact h.count r j hjr hjr' c hc hcj hcr
  · intro r e₁ e₂ he hpos
    rw [apply_τ] at hpos ⊢
    simp only [apply_hb, apply_cnt, apply_log, apply_n, apply_app]
    split_ifs at hpos ⊢ with hr
    · subst hr
      unfold merge at hpos ⊢
      split_ifs at hpos ⊢ with hm
      · rcases le_total (s.τ r e₁ e₂) ((s.log u).ts e₁ e₂) with hle | hle
        · rw [max_eq_right hle] at hpos ⊢
          obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.ts_wit u hun e₁ e₂ hm.2 hpos
          refine ⟨c, hc, hc1, hc2, hc3, ?_⟩
          rcases hc4 with rfl | hc4
          · exact Or.inl (Set.mem_insert _ _)
          · exact Or.inr ⟨u, Set.mem_insert _ _, hc4⟩
        · rw [max_eq_left hle] at hpos ⊢
          obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.τ_wit r e₁ e₂ he hpos
          refine ⟨c, hc, hc1, hc2, hc3, ?_⟩
          rcases hc4 with hc4 | ⟨d, hd, hcd⟩
          · exact Or.inl (Set.mem_insert_of_mem _ hc4)
          · exact Or.inr ⟨d, Set.mem_insert_of_mem _ hd, hcd⟩
      · obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.τ_wit r e₁ e₂ he hpos
        refine ⟨c, hc, hc1, hc2, hc3, ?_⟩
        rcases hc4 with hc4 | ⟨d, hd, hcd⟩
        · exact Or.inl (Set.mem_insert_of_mem _ hc4)
        · exact Or.inr ⟨d, Set.mem_insert_of_mem _ hd, hcd⟩
    · exact h.τ_wit r e₁ e₂ he hpos
  · exact h.ts_wit

omit h in
theorem step {s s' : State ι Reg} (h : Inv X s) (hs : Step X s s') : Inv X s' := by
  cases hs with
  | write i x hx => exact h.write hx
  | apply i a ha => exact h.apply ha

end Inv

/-- The invariant holds in every reachable state. -/
theorem Inv.of_reachable (hs : Reachable X s) : Inv X s := by
  obtain ⟨s₀, h₀, hrun⟩ := hs
  induction hrun with
  | refl => exact Inv.init h₀
  | tail _ hst ih => exact ih.step hst

end Podc.PartialReplicationCausal
