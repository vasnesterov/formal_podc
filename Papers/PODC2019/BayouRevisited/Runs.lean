import Papers.PODC2019.BayouRevisited.Blocks

/-!
# Infinite runs as limits of growing finite executions, and their histories
-/

-- CSLib candidate (infinite runs as limits of chains of finite executions)
namespace Podc.BayouRevisited

/-- The infinite sequence whose finite prefixes are the lists `C K`. -/
def limRun {α : Type} (C : ℕ → List α) (a₀ : α) (t : ℕ) : α := (C (t + 1)).getD t a₀

/-- A chain of finite executions: each is a prefix of the next and `C K` has length `≥ K`. -/
structure IsChain {α : Type} (C : ℕ → List α) : Prop where
  mono : ∀ K, C K <+: C (K + 1)
  grow : ∀ K, K ≤ (C K).length

namespace IsChain

variable {α : Type} {C : ℕ → List α} (hC : IsChain C)
include hC

lemma prefix_of_le {K K' : ℕ} (h : K ≤ K') : C K <+: C K' := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (hC.mono _)

lemma limRun_eq (a₀ : α) {K t : ℕ} (ht : t < (C K).length) : limRun C a₀ t = (C K)[t] := by
  have h1 : t < (C (t + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self t) (hC.grow _)
  rw [limRun, List.getD_eq_getElem _ _ h1]
  rcases le_total K (t + 1) with h | h
  · exact ((hC.prefix_of_le h).getElem ht).symm
  · exact (hC.prefix_of_le h).getElem h1

lemma pre_eq (a₀ : α) {K t : ℕ} (ht : t ≤ (C K).length) :
    (List.range t).map (limRun C a₀) = (C K).take t := by
  apply List.ext_getElem (by simp; omega)
  intro u h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  exact hC.limRun_eq a₀ (by simp at h1; omega)

lemma pre_eq_self (a₀ : α) (K : ℕ) : (List.range (C K).length).map (limRun C a₀) = C K := by
  rw [hC.pre_eq a₀ le_rfl, List.take_length]

lemma exists_eq_of_mem (a₀ : α) {K : ℕ} {a : α} (h : a ∈ C K) : ∃ t, limRun C a₀ t = a := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem h
  exact ⟨t, hC.limRun_eq a₀ ht⟩

lemma mem_of_eq (a₀ : α) (t : ℕ) : limRun C a₀ t ∈ C (t + 1) := by
  have h1 : t < (C (t + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self t) (hC.grow _)
  rw [hC.limRun_eq a₀ h1]; exact List.getElem_mem _

end IsChain

namespace Impl

variable {n : ℕ} {Op Val : Type} {I : Impl n Op Val} {S : ACTSpec Op Val}

lemma pre_limRun {C : ℕ → List I.Act} (hC : IsChain C) (a₀ : I.Act) (K : ℕ) :
    I.pre (limRun C a₀) (C K).length = C K := hC.pre_eq_self a₀ K

lemma pre_limRun_prefix {C : ℕ → List I.Act} (hC : IsChain C) (a₀ : I.Act) {K t : ℕ}
    (ht : t ≤ (C K).length) : I.pre (limRun C a₀) t <+: C K := by
  rw [pre, hC.pre_eq a₀ ht]; exact List.take_prefix _ _

lemma pre_prefix_of_le (r : ℕ → I.Act) {t t' : ℕ} (h : t ≤ t') : I.pre r t <+: I.pre r t' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨(List.range' t d).map r, ?_⟩
  rw [pre, pre, List.range_add, List.map_append]
  congr 1
  simp [List.range'_eq_map_range, List.map_map, Function.comp_def, Nat.add_comm]

lemma loc_prefix {P Q : List I.Act} (h : P <+: Q) (i : Fin n) : I.loc i P <+: I.loc i Q := by
  obtain ⟨R, rfl⟩ := h; rw [loc_append]; exact List.prefix_append _ _

lemma rbCasts_length_mono {ℓ ℓ' : List I.Input} (h : ℓ <+: ℓ') (j : Fin n) :
    (I.rbCasts j ℓ).length ≤ (I.rbCasts j ℓ').length := by
  obtain ⟨R, rfl⟩ := h; exact (I.rbCasts_prefix j ℓ R).length_le

lemma tobCasts_length_mono {ℓ ℓ' : List I.Input} (h : ℓ <+: ℓ') (j : Fin n) :
    (I.tobCasts j ℓ).length ≤ (I.tobCasts j ℓ').length := by
  obtain ⟨R, rfl⟩ := h; exact (I.tobCasts_prefix j ℓ R).length_le

lemma lresp_mono {ℓ ℓ' : List I.Input} (h : ℓ <+: ℓ') {i : Fin n} {c : ℕ} {v : Val}
    (hv : I.lresp i ℓ c = some v) : I.lresp i ℓ' c = some v := by
  obtain ⟨R, rfl⟩ := h; exact I.lresp_append hv R

/-! ### Runs from chains -/

variable {C : ℕ → List I.Act}

lemma validRun_lim (hC : IsChain C) (a₀ : I.Act) (hV : ∀ K, I.Valid S (C K)) :
    I.ValidRun S (limRun C a₀) := by
  intro t
  have h1 : t < (C (t + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self t) (hC.grow _)
  have := hV (t + 1) t h1
  rw [pre, hC.pre_eq a₀ h1.le, hC.limRun_eq a₀ h1]
  exact this

lemma fair_lim (hC : IsChain C) (a₀ : I.Act)
    (hinv : ∀ K i, ∃ x, (i, x) ∈ (C (K + 1)).drop (C K).length ∧ x.IsInv)
    (hpas : ∀ K i, I.Passive i (I.lstate i (I.loc i (C (K + 1)))))
    (hrb : ∀ K i j k, k < (I.rbCasts j (I.loc j (C K))).length →
      ∃ m, (i, LIn.rb j k m) ∈ C (K + 1)) :
    I.Fair (limRun C a₀) where
  inv_inf i N := by
    obtain ⟨x, hx, hxi⟩ := hinv N i
    obtain ⟨u, hu, hue⟩ := List.getElem_of_mem hx
    simp only [List.length_drop] at hu
    have hlt : (C N).length + u < (C (N + 1)).length := by omega
    refine ⟨(C N).length + u, le_trans (hC.grow N) (Nat.le_add_right _ _), ?_⟩
    rw [hC.limRun_eq a₀ hlt]
    rw [List.getElem_drop] at hue
    rw [hue]; exact ⟨rfl, hxi⟩
  passive_inf i N := ⟨(C (N + 1)).length, le_trans (Nat.le_succ N) (hC.grow _), by
    rw [pre_limRun hC]; exact hpas N i⟩
  rb_all i j k t hk := by
    have hp := pre_limRun_prefix hC a₀ (hC.grow t)
    have := rbCasts_length_mono (loc_prefix hp j) j
    obtain ⟨m, hm⟩ := hrb t i j k (by omega)
    obtain ⟨t', ht'⟩ := hC.exists_eq_of_mem a₀ hm
    exact ⟨t', m, ht'⟩

lemma tobLive_lim (hC : IsChain C) (a₀ : I.Act)
    (htob : ∀ K i j k, k < (I.tobCasts j (I.loc j (C K))).length →
      ∃ m, (i, LIn.tob j k m) ∈ C (K + 1)) :
    ∀ i j k t, k < (I.tobCasts j (I.loc j (I.pre (limRun C a₀) t))).length →
      ∃ t' m, limRun C a₀ t' = (i, .tob j k m) := by
  intro i j k t hk
  have hp := pre_limRun_prefix hC a₀ (hC.grow t)
  have := tobCasts_length_mono (loc_prefix hp j) j
  obtain ⟨m, hm⟩ := htob t i j k (by omega)
  obtain ⟨t', ht'⟩ := hC.exists_eq_of_mem a₀ hm
  exact ⟨t', m, ht'⟩

lemma tobAgree_of_live {r : ℕ → I.Act} (hV : I.ValidRun S r)
    (hlive : ∀ i j k t, k < (I.tobCasts j (I.loc j (I.pre r t))).length →
      ∃ t' m, r t' = (i, .tob j k m)) :
    ∀ i j k m t, r t = (i, .tob j k m) → ∀ i', ∃ t' m', r t' = (i', .tob j k m') := by
  intro i j k m t ht i'
  have h := hV t
  rw [ht] at h
  exact hlive i' j k t (List.getElem?_eq_some_iff.1 h.1).1

lemma isStableRun_lim (hC : IsChain C) (a₀ : I.Act) (hV : ∀ K, I.Valid S (C K))
    (hinv : ∀ K i, ∃ x, (i, x) ∈ (C (K + 1)).drop (C K).length ∧ x.IsInv)
    (hpas : ∀ K i, I.Passive i (I.lstate i (I.loc i (C (K + 1)))))
    (hrb : ∀ K i j k, k < (I.rbCasts j (I.loc j (C K))).length →
      ∃ m, (i, LIn.rb j k m) ∈ C (K + 1))
    (htob : ∀ K i j k, k < (I.tobCasts j (I.loc j (C K))).length →
      ∃ m, (i, LIn.tob j k m) ∈ C (K + 1)) :
    I.IsStableRun S (limRun C a₀) := by
  have hVR := validRun_lim hC a₀ hV
  have hlive := tobLive_lim hC a₀ htob
  exact ⟨⟨hVR, fair_lim hC a₀ hinv hpas hrb, tobAgree_of_live hVR hlive⟩, hlive⟩

lemma isAsyncRun_lim_noTob (hC : IsChain C) (a₀ : I.Act) (hV : ∀ K, I.Valid S (C K))
    (hinv : ∀ K i, ∃ x, (i, x) ∈ (C (K + 1)).drop (C K).length ∧ x.IsInv)
    (hpas : ∀ K i, I.Passive i (I.lstate i (I.loc i (C (K + 1)))))
    (hrb : ∀ K i j k, k < (I.rbCasts j (I.loc j (C K))).length →
      ∃ m, (i, LIn.rb j k m) ∈ C (K + 1))
    (hnotob : ∀ K i j k m, (i, LIn.tob j k m) ∉ C K) :
    I.IsAsyncRun S (limRun C a₀) := by
  refine ⟨validRun_lim hC a₀ hV, fair_lim hC a₀ hinv hpas hrb, ?_⟩
  intro i j k m t ht
  exact absurd (ht ▸ hC.mem_of_eq a₀ t) (hnotob _ i j k m)

/-! ### Histories -/

variable (I)

/-- The value returned by the weak invocation of `op` at replica `i` after local inputs `ℓ`
(its response in the same step). -/
def immVal (i : Fin n) (ℓ : List I.Input) (op : Op) : Option Val :=
  (I.stepAt i ℓ (.inv op .weak)).2.resp.lookup ℓ.length

variable {I}

lemma lresp_concat_self (i : Fin n) (ℓ : List I.Input) (x : I.Input) :
    I.lresp i (ℓ ++ [x]) ℓ.length = (I.stepAt i ℓ x).2.resp.lookup ℓ.length := by
  simp only [lresp, leffs_concat]
  rw [List.drop_append_of_le_length (by simp)]
  rw [show List.drop ℓ.length (I.leffs i ℓ) = [] from
    List.drop_eq_nil_of_le (by simp), List.nil_append, List.findSome?_singleton]

lemma rvalOf_eq_of_lresp {r : ℕ → I.Act} (e : I.Ev r) {T : ℕ} {v : Val}
    (h : I.lresp (r e.1).1 (I.loc (r e.1).1 (I.pre r T)) (I.lidx r e.1) = some v) :
    I.rvalOf r e = some v := by
  classical
  have hex : ∃ T v, I.lresp (r e.1).1 (I.loc (r e.1).1 (I.pre r T)) (I.lidx r e.1) = some v :=
    ⟨T, v, h⟩
  rw [rvalOf, dif_pos hex]
  congr 1
  have hs := hex.choose_spec.choose_spec
  rcases le_total T hex.choose with hle | hle
  · have := lresp_mono (loc_prefix (pre_prefix_of_le r hle) _) h
    exact Option.some_inj.1 (hs.symm.trans this)
  · have := lresp_mono (loc_prefix (pre_prefix_of_le r hle) _) hs
    exact Option.some_inj.1 (this.symm.trans h)

lemma exists_lresp_of_rvalOf {r : ℕ → I.Act} (e : I.Ev r) {v : Val}
    (h : I.rvalOf r e = some v) :
    ∃ T, I.lresp (r e.1).1 (I.loc (r e.1).1 (I.pre r T)) (I.lidx r e.1) = some v := by
  classical
  by_cases hex : ∃ T v, I.lresp (r e.1).1 (I.loc (r e.1).1 (I.pre r T)) (I.lidx r e.1) = some v
  · obtain ⟨T, w, hw⟩ := hex
    rw [rvalOf_eq_of_lresp e hw] at h
    cases h; exact ⟨T, hw⟩
  · rw [rvalOf, dif_neg hex] at h; cases h

lemma rb_of_rvalOf {r : ℕ → I.Act} {e₁ e₂ : I.Ev r} {v : Val} (h : I.rvalOf r e₁ = some v)
    {T : ℕ} (hT : I.lresp (r e₁.1).1 (I.loc (r e₁.1).1 (I.pre r T)) (I.lidx r e₁.1) = some v)
    (hle : T ≤ e₂.1) : (I.history r).rb e₁ e₂ := by
  have := lresp_mono (loc_prefix (pre_prefix_of_le r hle) _) hT
  simp only [history, this, Option.isSome_some]

end Impl

end Podc.BayouRevisited
