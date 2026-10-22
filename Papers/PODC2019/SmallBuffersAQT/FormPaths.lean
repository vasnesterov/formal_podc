import Papers.PODC2019.SmallBuffersAQT.RoundBad

/-!
# The loop of `FormPaths` (Algorithm 4) equals the closed form `fpAct`

Algorithm 4 on a level-`λ` interval with intermediate destinations `w_0 < ⋯ < w_{m-1}`:
```
i' ← w_{m-1}
for k ← m-1 downto 0:
  if some i'' < i' is bad for w_k:
    i_k ← min {i'' : L_{λ,k}(i'') bad};  activate [i_k, min(i'-1, w_k-1)] for w_k;  i' ← i_k
```
`loopAct ws ptr v` is the destination activated at node `v` by this loop, run on the list
`ws = [w_{m-1}, …, w_0]` with initial pointer `ptr = w_{m-1}`, for an abstract badness relation
`bad u w` (`u` holds a bad pseudo-buffer for `w`). `loopAct_eq_find` shows that it is the first
(= largest) `w` in `ws` with `v < w` and a bad node `u ≤ v` (for `v < ptr`), and `fpAct_eq_loop`
identifies this with `fpAct`.
-/

namespace Podc.SmallBuffersAQT

open Finset Classical

section Loop

variable (bad : ℕ → ℕ → Prop)

/-- The activation produced at node `v` by the loop of Algorithm 4. -/
noncomputable def loopAct : List ℕ → ℕ → ℕ → Option ℕ
  | [], _, _ => none
  | w :: ws, ptr, v =>
    if h : ∃ u, u < ptr ∧ bad u w then
      if Nat.find (⟨h.choose, h.choose_spec.2⟩ : ∃ u, bad u w) ≤ v ∧ v < min ptr w then some w
      else loopAct ws (Nat.find (⟨h.choose, h.choose_spec.2⟩ : ∃ u, bad u w)) v
    else loopAct ws ptr v

/-- The closed form: the first destination of the list that has to be crossed at `v` and has a
bad pseudo-buffer at or before `v`. -/
noncomputable def closedAct (ws : List ℕ) (v : ℕ) : Option ℕ :=
  ws.find? (fun w => decide (v < w ∧ ∃ u ≤ v, bad u w))

variable {bad}

lemma loopAct_of_le : ∀ (ws : List ℕ) (ptr v : ℕ), ptr ≤ v → loopAct bad ws ptr v = none
  | [], _, _, _ => rfl
  | w :: ws, ptr, v, h => by
    unfold loopAct
    split_ifs with h1 h2
    · omega
    · exact loopAct_of_le ws _ v (by
        have := Nat.find_le (h := (⟨h1.choose, h1.choose_spec.2⟩ : ∃ u, bad u w)) h1.choose_spec.2
        have := h1.choose_spec.1; omega)
    · exact loopAct_of_le ws ptr v h

lemma closedAct_of_le : ∀ (ws : List ℕ) (v : ℕ), (∀ w ∈ ws, w ≤ v) → closedAct bad ws v = none
  | [], _, _ => rfl
  | w :: ws, v, h => by
    unfold closedAct
    rw [List.find?_cons_of_neg]
    · exact closedAct_of_le ws v (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    · have := h w List.mem_cons_self
      simp only [decide_eq_true_eq, not_and, not_exists]
      intro h'; omega

/-- The loop computes the closed form, below the pointer. -/
theorem loopAct_eq_find : ∀ (ws : List ℕ), ws.Pairwise (· > ·) → (∀ u, ∀ w ∈ ws, bad u w → u < w) →
    ∀ ptr v, v < ptr → loopAct bad ws ptr v = closedAct bad ws v
  | [], _, _, _, _, _ => rfl
  | w :: ws, hs, hb, ptr, v, hv => by
    have hs' := List.pairwise_cons.1 hs
    have hb' : ∀ u, ∀ w' ∈ ws, bad u w' → u < w' := fun u w' hw' => hb u w' (List.mem_cons_of_mem _ hw')
    unfold loopAct closedAct
    split_ifs with h1 h2
    · -- `v` lies in the run of `w`
      rw [List.find?_cons_of_pos]
      simp only [decide_eq_true_eq]
      exact ⟨by omega, Nat.find (⟨h1.choose, h1.choose_spec.2⟩ : ∃ u, bad u w), h2.1,
        Nat.find_spec (⟨h1.choose, h1.choose_spec.2⟩ : ∃ u, bad u w)⟩
    · set i := Nat.find (⟨h1.choose, h1.choose_spec.2⟩ : ∃ u, bad u w) with hi
      have hiptr : i < ptr := lt_of_le_of_lt (Nat.find_le h1.choose_spec.2) h1.choose_spec.1
      rcases Nat.lt_or_ge v i with hvi | hvi
      · -- `v` is left of the run: `w` has no bad node `≤ v`
        rw [loopAct_eq_find ws hs'.2 hb' i v hvi, List.find?_cons_of_neg]
        · rfl
        · simp only [decide_eq_true_eq, not_and, not_exists]
          intro _ u hu hbu
          exact Nat.find_min (⟨h1.choose, h1.choose_spec.2⟩ : ∃ u, bad u w) (by omega) hbu
      · -- `v ≥ w`: nothing is activated at `v` any more
        have hvw : w ≤ v := by
          have : ¬ (v < min ptr w) := fun h => h2 ⟨hvi, h⟩
          omega
        rw [loopAct_of_le ws i v hvi, List.find?_cons_of_neg]
        · exact (closedAct_of_le ws v (fun w' hw' => by have := hs'.1 w' hw'; omega)).symm
        · simp only [decide_eq_true_eq, not_and, not_exists]
          intro h; omega
    · -- no bad node of `w` before the pointer
      rw [loopAct_eq_find ws hs'.2 hb' ptr v hv, List.find?_cons_of_neg]
      · rfl
      · simp only [decide_eq_true_eq, not_and, not_exists]
        intro _ u hu hbu
        exact h1 ⟨u, by omega, hbu⟩

end Loop

variable {m ℓ : ℕ} {c : Config} {lam : ℕ}

/-- The intermediate destinations of the level-`lam` interval `[b, b + m^(lam+1))`, in decreasing
order: `[w_{m-1}, …, w_0]` with `w_k = b + k m^lam`. -/
def destList (m lam b : ℕ) : List ℕ := ((List.range m).reverse).map (fun k => b + k * m ^ lam)

lemma destList_pairwise (hm : 0 < m) (b : ℕ) : (destList m lam b).Pairwise (· > ·) := by
  unfold destList
  rw [List.pairwise_map]
  refine List.Pairwise.imp (fun {a a'} h => ?_) (List.pairwise_reverse.2 (List.pairwise_lt_range))
  have : 0 < m ^ lam := pow_pos hm _
  nlinarith

lemma mem_destList {b x : ℕ} : x ∈ destList m lam b ↔ ∃ k < m, x = b + k * m ^ lam := by
  simp [destList, eq_comm]

/-- Every bad level-`lam` pseudo-buffer has an intermediate destination of the interval. -/
lemma xd_mem_destList {u w : ℕ} (huw : u < w) (hw : w < m ^ ℓ) (hlv : lv m ℓ u w = lam) :
    xd m ℓ u w ∈ destList m lam (lvl m lam u) := by
  have hm := (two_le_of_lt huw hw).1
  have hk := key_mem_image (m := m) (ℓ := ℓ) huw hw
  simp only [mem_image, mem_product, mem_range, key, Prod.mk.injEq] at hk
  obtain ⟨⟨j, d⟩, ⟨-, hd⟩, hj, hx⟩ := hk
  simp only at hj hx hd
  subst hj
  rw [mem_destList]
  exact ⟨d, hd, by rw [← hx, hlv]; rfl⟩

/-- The closed form `fpAct` is the activation of the loop of Algorithm 4 run on the level-`lam`
interval of `v` (for `v` below the last intermediate destination of its interval; above it both
are inactive). -/
theorem fpAct_eq_loop (hm : 2 ≤ m) (v : ℕ) :
    fpAct m ℓ c lam v =
      (loopAct (fun u w => 2 ≤ pb m ℓ c u (lam, w)) (destList m lam (lvl m lam v))
        (lvl m lam v + (m - 1) * m ^ lam) v).map (fun x => (lam, x)) := by
  set b := lvl m lam v
  set bad : ℕ → ℕ → Prop := fun u w => 2 ≤ pb m ℓ c u (lam, w)
  -- facts about bad pseudo-buffers
  have hbad : ∀ u w, bad u w → ∃ w', u < w' ∧ w' < m ^ ℓ ∧ key m ℓ u w' = (lam, w) := by
    intro u w h
    obtain ⟨w', h1, h2, h3, -⟩ := pb_pos (by simp only [bad] at h; omega : 1 ≤ pb m ℓ c u (lam, w))
    exact ⟨w', h1, h2, h3⟩
  have hlt : ∀ u, ∀ w ∈ destList m lam b, bad u w → u < w := by
    intro u w _ h
    obtain ⟨w', h1, h2, h3⟩ := hbad u w h
    have := lt_xd h1 h2
    simp only [key, Prod.mk.injEq] at h3
    rw [← h3.2]; exact this
  -- a bad pseudo-buffer crossing `v` belongs to the interval of `v`
  have hin : ∀ u x, u ≤ v → v < x → bad u x → x ∈ destList m lam b := by
    intro u x huv hvx h
    obtain ⟨w', h1, h2, h3⟩ := hbad u x h
    simp only [key, Prod.mk.injEq] at h3
    have hmem := xd_mem_destList h1 h2 h3.1
    rw [h3.2] at hmem
    have hb : lvl m lam u = b := by
      apply lvl_eq_of_div_eq
      have := div_eq_of_key h1 h2 huv (by rw [h3.2]; exact hvx)
      rwa [h3.1] at this
    rwa [hb] at hmem
  have hpos : 0 < m ^ lam := pow_pos (by omega) _
  rcases Nat.lt_or_ge v (b + (m - 1) * m ^ lam) with hvt | hvt
  · rw [loopAct_eq_find _ (destList_pairwise (by omega) b) hlt _ v hvt]
    -- compare the maximum with the first element of the decreasing list
    unfold closedAct
    rcases hf : fpAct m ℓ c lam v with _ | q
    · -- nothing to activate
      symm
      rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro x hx
      simp only [decide_eq_true_eq, not_and, not_exists]
      intro hvx u hu hbu
      obtain ⟨-, hxn⟩ : x ∈ destList m lam b ∧ x < m ^ ℓ := by
        obtain ⟨w', h1, h2, h3⟩ := hbad u x hbu
        simp only [key, Prod.mk.injEq] at h3
        exact ⟨hx, h3.2 ▸ (xd_le u w').trans_lt h2⟩
      exact fpAct_ne_none_of hxn hvx hu hbu hf
    · obtain ⟨hq1, hq2, hq3, u, hu, hbu⟩ := fpAct_eq_some hf
      have hqe : q = (lam, q.2) := by rw [← hq1]
      have hbq : bad u q.2 := by simp only [bad]; rw [← hqe]; exact hbu
      have hmemq := hin u q.2 hu hq2 hbq
      -- `q.2` is the first element of the list satisfying the predicate
      have hfind : (destList m lam b).find? (fun w => decide (v < w ∧ ∃ u ≤ v, bad u w)) = some q.2 := by
        rw [List.find?_eq_some_iff_append]
        refine ⟨by simp only [decide_eq_true_eq]; exact ⟨hq2, u, hu, hbq⟩, ?_⟩
        obtain ⟨as, bs, hab⟩ := List.append_of_mem hmemq
        refine ⟨as, bs, hab, fun a ha => ?_⟩
        have hs := destList_pairwise (lam := lam) (by omega : 0 < m) b
        rw [hab, List.pairwise_append] at hs
        have hgt : a > q.2 := hs.2.2 a ha q.2 List.mem_cons_self
        rw [Bool.not_eq_true', decide_eq_false_iff_not]
        rintro ⟨hva, u', hu', hbu'⟩
        have han : a < m ^ ℓ := by
          obtain ⟨w', h1, h2, h3⟩ := hbad u' a hbu'
          simp only [key, Prod.mk.injEq] at h3
          exact h3.2 ▸ (xd_le u' w').trans_lt h2
        have := fpAct_max hf han hva hu' hbu'
        omega
      rw [hqe]
      convert (congrArg (Option.map (fun x => (lam, x))) hfind).symm using 1
      · rfl
      · congr! 3
  · -- `v` is at or beyond the last intermediate destination: both inactive
    rw [loopAct_of_le _ _ v hvt]
    simp only [Option.map_none]
    by_contra hne
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨hq1, hq2, -, u, hu, hbu⟩ := fpAct_eq_some hq
    have hqe : q = (lam, q.2) := by rw [← hq1]
    have hmem := hin u q.2 hu hq2 (by simp only [bad]; rw [← hqe]; exact hbu)
    rw [mem_destList] at hmem
    obtain ⟨k, hk, hx⟩ := hmem
    have : k * m ^ lam ≤ (m - 1) * m ^ lam := Nat.mul_le_mul_right _ (by omega)
    omega

end Podc.SmallBuffersAQT
